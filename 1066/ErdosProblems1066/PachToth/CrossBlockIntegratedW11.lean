import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11
import ErdosProblems1066.PachToth.GeneratedPointClosureW11
import ErdosProblems1066.PachToth.FlexibleTransitionClosureW11
import ErdosProblems1066.PachToth.RoleHingePolynomialReductionW11

set_option autoImplicit false

/-!
# W11 integrated cross-block matrix

This file is a source-facing integration layer for W11 cross-block data.  It
collects the checked row adapters from the cross-block inequality ledger, the
generated-point closure, the flexible transition closure, and the reduced
role-hinge inequality package.

Every target row below is conditional on an explicit input package.  Missing
numeric inequality rows remain fields of those packages; this module only
records how such fields route to separation, closed placements, exact targets,
and checked arbitrary targets.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockIntegratedW11

noncomputable section

universe u

abbrev PeriodSearchFamily :=
  GeneratedPointCertificateW11.RoleHingedPeriodSearchFamily

abbrev RoleHingePeriodSearchFamily :=
  RoleHingePolynomialReductionW11.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockInequalityLedgerW11.LocalVertexIndex

abbrev GeneratedGlobalSeparationAt
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) : Prop :=
  GeneratedPointCertificateW11.GeneratedGlobalSeparationAt F k hk

abbrev CrossBlockClosureLedger (F : PeriodSearchFamily) :=
  CrossBlockInequalityClosureW11.CrossBlockClosureLedger F

abbrev CrossBlockInequalityLedger (F : PeriodSearchFamily) :=
  CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger F

abbrev PolynomialRows (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockInequalityLedgerW11.UpperTriangleGeneratedPointPolynomialRows
    F k hk

abbrev ValueRows (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockInequalityLedgerW11.UpperTriangleGeneratedPointValueRows F k hk

abbrev PolynomialRowFamilies (F : PeriodSearchFamily) :=
  CrossBlockInequalityLedgerW11.UpperTriangleGeneratedPointPolynomialRowFamilies
    F

abbrev ValueRowFamilies (F : PeriodSearchFamily) :=
  CrossBlockInequalityLedgerW11.UpperTriangleGeneratedPointValueRowFamilies F

abbrev LengthTwoRows (F : PeriodSearchFamily) :=
  CrossBlockInequalityLedgerW11.LengthTwoLocalVertexRows F

abbrev GeneratedPointTable (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockInequalityLedgerW11.GeneratedPointNonConnectorPolynomialTable
    F k hk

abbrev PackedInequalities (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockInequalityLedgerW11.PackedNonConnectorPolynomialInequalities
    F k hk

abbrev NonConnectorValueMatrix
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockInequalityLedgerW11.NonConnectorValueMatrix F k hk

abbrev NonConnectorLowerTable
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockInequalityLedgerW11.NonConnectorLowerTable F k hk

abbrev PositionPolynomialCertificate
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockInequalityLedgerW11.PositionPolynomialCertificate F k hk

abbrev PositionValueCertificate
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockInequalityLedgerW11.PositionValueCertificate F k hk

abbrev SqDistanceTable
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockInequalityLedgerW11.IndexedNonConnectorCrossBlockSqDistanceTable
    F k hk

abbrev NonConnectorValueMatrixFamily (F : PeriodSearchFamily) :=
  CrossBlockInequalityLedgerW11.NonConnectorValueMatrixFamily F

abbrev NonConnectorLowerTableFamily (F : PeriodSearchFamily) :=
  CrossBlockInequalityLedgerW11.NonConnectorLowerTableFamily F

abbrev NormalizedPolynomialFields (F : PeriodSearchFamily) :=
  GeneratedPointCertificateW11.NormalizedPolynomialFields F

abbrev NormalizedValueFields (F : PeriodSearchFamily) :=
  GeneratedPointCertificateW11.NormalizedValueFields F

abbrev LowerBoundFields (F : PeriodSearchFamily) :=
  GeneratedPointCertificateW11.LowerBoundFields F

abbrev RoleHingeCrossBlockInequalityPackage
    (F : RoleHingePeriodSearchFamily) :=
  RoleHingePolynomialReductionW11.CrossBlockInequalityPackage F

abbrev FlexibleTransitionRouteFields :=
  FlexibleTransitionClosureW11.TransitionRouteFields

abbrev FlexibleCandidateAssemblyFields :=
  FlexibleTransitionClosureW11.CandidateAssemblyFields

abbrev ClosedPlacementPackage :=
  ArbitraryNBridgeW10.ClosedPlacementPackage

/-! ## Shared route rows -/

/-- A target row whose fixed and arbitrary conclusions are obtained from an
exact target through the checked finite-remainder route. -/
structure CheckedTargetRow (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

namespace CheckedTargetRow

/-- Build a checked target row from an exact-target projection. -/
def ofExactTarget
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen) :
    CheckedTargetRow alpha where
  exactTarget := exactTarget
  fixedTarget := fun a n =>
    (ArbitraryNBridgeW10.checkedRemainderRouteRow exactTarget).fixedTarget a n
  arbitraryTarget := fun a =>
    (ArbitraryNBridgeW10.checkedRemainderRouteRow exactTarget).arbitraryTarget a

/-- Reuse a generated-point closure row, but route its arbitrary conclusion
through the checked finite-remainder bridge. -/
def ofGeneratedPointTargetRow
    {alpha : Sort u}
    (R : GeneratedPointClosureW11.GeneratedPointTargetRow alpha) :
    CheckedTargetRow alpha :=
  ofExactTarget R.exactTarget

/-- Reuse a flexible-transition closure row, with the same checked arbitrary
target route. -/
def ofFlexibleStrongTargetRow
    {alpha : Sort u}
    (R : FlexibleTransitionClosureW11.StrongTargetRow alpha) :
    CheckedTargetRow alpha :=
  ofExactTarget R.exactTarget

end CheckedTargetRow

/-- Fixed-period row: one explicit row or certificate package gives generated
separation for that period, hence a closed placement and the exact block
target for `16 * k`. -/
structure BlockRouteRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k)
    (alpha : Sort u) : Sort (max 1 u) where
  separated : alpha -> GeneratedGlobalSeparationAt F k hk
  closedPlacement :
    alpha -> DeformedPlacement.ClosedPlacement k hk
  exactBlockTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenAt (16 * k)

namespace BlockRouteRow

/-- Build the fixed-period row from generated separation. -/
def ofSeparation
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    {alpha : Sort u}
    (separated : alpha -> GeneratedGlobalSeparationAt F k hk) :
    BlockRouteRow F k hk alpha where
  separated := separated
  closedPlacement := fun a =>
    GeneratedPointCertificateW11.closedPlacementOfSeparation
      F (k := k) hk (separated a)
  exactBlockTarget := fun a =>
    GeneratedPointCertificateW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_separation
      F (k := k) hk (separated a)

end BlockRouteRow

/-- Convert a generated-separation family into closed placements for every
positive block count. -/
def closedPlacementPackageOfSeparation
    {F : PeriodSearchFamily}
    (separated :
      forall (k : Nat) (hk : 0 < k), GeneratedGlobalSeparationAt F k hk) :
    ClosedPlacementPackage where
  placement := fun k hk =>
    GeneratedPointCertificateW11.closedPlacementOfSeparation
      F (k := k) hk (separated k hk)

/-- Family row: explicit fields for all positive periods give generated
separation, closed placements, exact targets, and checked arbitrary targets. -/
structure FamilyRouteRow
    (F : PeriodSearchFamily) (alpha : Sort u) : Sort (max 1 u) where
  separated :
    alpha -> forall (k : Nat) (hk : 0 < k),
      GeneratedGlobalSeparationAt F k hk
  closedPlacement :
    alpha -> forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk
  exactBlockTarget :
    alpha -> forall (k : Nat) (_hk : 0 < k),
      PachToth.targetUpperConstructionFiveSixteenAt (16 * k)
  checkedTargets : CheckedTargetRow alpha

namespace FamilyRouteRow

/-- Build a family route row from generated separation for every positive
block count. -/
def ofSeparation
    {F : PeriodSearchFamily} {alpha : Sort u}
    (separated :
      alpha -> forall (k : Nat) (hk : 0 < k),
        GeneratedGlobalSeparationAt F k hk) :
    FamilyRouteRow F alpha where
  separated := separated
  closedPlacement := fun a k hk =>
    GeneratedPointCertificateW11.closedPlacementOfSeparation
      F (k := k) hk (separated a k hk)
  exactBlockTarget := fun a k hk =>
    GeneratedPointCertificateW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_separation
      F (k := k) hk (separated a k hk)
  checkedTargets :=
    CheckedTargetRow.ofExactTarget
      (fun a =>
        (closedPlacementPackageOfSeparation (separated a))
          |>.targetUpperConstructionFiveSixteen)

theorem exactTarget
    {F : PeriodSearchFamily} {alpha : Sort u}
    (R : FamilyRouteRow F alpha) (a : alpha) :
    PachToth.targetUpperConstructionFiveSixteen :=
  R.checkedTargets.exactTarget a

theorem fixedTarget
    {F : PeriodSearchFamily} {alpha : Sort u}
    (R : FamilyRouteRow F alpha) (a : alpha) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  R.checkedTargets.fixedTarget a n

theorem arbitraryTarget
    {F : PeriodSearchFamily} {alpha : Sort u}
    (R : FamilyRouteRow F alpha) (a : alpha) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  R.checkedTargets.arbitraryTarget a

end FamilyRouteRow

/-! ## Fixed-period row and certificate routes -/

def polynomialRowsBlockRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :
    BlockRouteRow F k hk (PolynomialRows F k hk) :=
  BlockRouteRow.ofSeparation
    (fun R => by
      simpa [GeneratedGlobalSeparationAt] using R.generatedGlobalSeparation)

def valueRowsBlockRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :
    BlockRouteRow F k hk (ValueRows F k hk) :=
  BlockRouteRow.ofSeparation
    (fun R => by
      simpa [GeneratedGlobalSeparationAt] using R.generatedGlobalSeparation)

def generatedPointTableBlockRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :
    BlockRouteRow F k hk (GeneratedPointTable F k hk) :=
  BlockRouteRow.ofSeparation
    (fun T => by
      simpa [GeneratedGlobalSeparationAt] using
        CrossBlockInequalityLedgerW11.generatedGlobalSeparation_of_generatedPointTable
          (F := F) (k := k) (hk := hk) T)

def packedInequalitiesBlockRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :
    BlockRouteRow F k hk (PackedInequalities F k hk) :=
  BlockRouteRow.ofSeparation
    (fun C => by
      simpa [GeneratedGlobalSeparationAt] using
        CrossBlockInequalityLedgerW11.generatedGlobalSeparation_of_packedInequalities
          (F := F) (k := k) (hk := hk) C)

def valueMatrixBlockRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :
    BlockRouteRow F k hk (NonConnectorValueMatrix F k hk) :=
  BlockRouteRow.ofSeparation
    (fun M => by
      simpa [GeneratedGlobalSeparationAt] using
        CrossBlockInequalityLedgerW11.generatedGlobalSeparation_of_valueMatrix
          (F := F) (k := k) (hk := hk) M)

def lowerTableBlockRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :
    BlockRouteRow F k hk (NonConnectorLowerTable F k hk) :=
  BlockRouteRow.ofSeparation
    (fun T => by
      simpa [GeneratedGlobalSeparationAt] using
        CrossBlockInequalityLedgerW11.generatedGlobalSeparation_of_lowerTable
          (F := F) (k := k) (hk := hk) T)

def positionPolynomialCertificateBlockRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :
    BlockRouteRow F k hk (PositionPolynomialCertificate F k hk) :=
  BlockRouteRow.ofSeparation
    (fun C => by
      simpa [GeneratedGlobalSeparationAt] using
        CrossBlockInequalityLedgerW11.generatedGlobalSeparation_of_positionPolynomialCertificate
          (F := F) (k := k) (hk := hk) C)

def positionValueCertificateBlockRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :
    BlockRouteRow F k hk (PositionValueCertificate F k hk) :=
  BlockRouteRow.ofSeparation
    (fun C => by
      simpa [GeneratedGlobalSeparationAt] using
        CrossBlockInequalityLedgerW11.generatedGlobalSeparation_of_positionValueCertificate
          (F := F) (k := k) (hk := hk) C)

def sqDistanceTableBlockRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :
    BlockRouteRow F k hk (SqDistanceTable F k hk) :=
  BlockRouteRow.ofSeparation
    (fun T => by
      simpa [GeneratedGlobalSeparationAt] using
        CrossBlockInequalityLedgerW11.generatedGlobalSeparation_of_sqDistanceTable
          (F := F) (k := k) (hk := hk) T)

def lengthTwoRowsBlockRow
    (F : PeriodSearchFamily) :
    BlockRouteRow
      F 2 CrossBlockValueSearchW10.twoPositive (LengthTwoRows F) :=
  BlockRouteRow.ofSeparation
    (fun R => by
      simpa [GeneratedGlobalSeparationAt] using R.generatedGlobalSeparation)

/-! ## Family routes -/

def polynomialRowFamiliesRow
    (F : PeriodSearchFamily) :
    FamilyRouteRow F (PolynomialRowFamilies F) :=
  FamilyRouteRow.ofSeparation
    (fun R k hk => by
      simpa [GeneratedGlobalSeparationAt] using R.separated k hk)

def valueRowFamiliesRow
    (F : PeriodSearchFamily) :
    FamilyRouteRow F (ValueRowFamilies F) :=
  FamilyRouteRow.ofSeparation
    (fun R k hk => by
      simpa [GeneratedGlobalSeparationAt] using R.separated k hk)

def valueMatrixFamilyRow
    (F : PeriodSearchFamily) :
    FamilyRouteRow F (NonConnectorValueMatrixFamily F) :=
  FamilyRouteRow.ofSeparation
    (fun M k hk => by
      simpa [GeneratedGlobalSeparationAt] using
        CrossBlockInequalityLedgerW11.separated_of_valueMatrixFamily
          (F := F) M k hk)

def lowerTableFamilyRow
    (F : PeriodSearchFamily) :
    FamilyRouteRow F (NonConnectorLowerTableFamily F) :=
  FamilyRouteRow.ofSeparation
    (fun T k hk => by
      simpa [GeneratedGlobalSeparationAt] using
        CrossBlockInequalityLedgerW11.separated_of_lowerTableFamily
          (F := F) T k hk)

def crossBlockInequalityLedgerRow
    (F : PeriodSearchFamily) :
    FamilyRouteRow F (CrossBlockInequalityLedger F) :=
  FamilyRouteRow.ofSeparation
    (fun L k hk => by
      simpa [GeneratedGlobalSeparationAt] using L.separated k hk)

def crossBlockClosureLedgerRow
    (F : PeriodSearchFamily) :
    FamilyRouteRow F (CrossBlockClosureLedger F) :=
  FamilyRouteRow.ofSeparation
    (fun C k hk => by
      simpa [GeneratedGlobalSeparationAt] using
        C.generatedGlobalSeparation k hk)

def normalizedPolynomialFieldsFamilyRow
    (F : PeriodSearchFamily) :
    FamilyRouteRow F (NormalizedPolynomialFields F) :=
  FamilyRouteRow.ofSeparation
    (fun C k hk => C.separated k hk)

def normalizedValueFieldsFamilyRow
    (F : PeriodSearchFamily) :
    FamilyRouteRow F (NormalizedValueFields F) :=
  FamilyRouteRow.ofSeparation
    (fun C k hk => C.separated k hk)

def lowerBoundFieldsFamilyRow
    (F : PeriodSearchFamily) :
    FamilyRouteRow F (LowerBoundFields F) :=
  FamilyRouteRow.ofSeparation
    (fun C k hk => C.separated k hk)

/-! ## Target rows imported from adjacent closure matrices -/

def generatedPointNormalizedPolynomialTargetRow
    (F : PeriodSearchFamily) :
    CheckedTargetRow (NormalizedPolynomialFields F) :=
  CheckedTargetRow.ofGeneratedPointTargetRow
    (GeneratedPointClosureW11.matrix.normalizedPolynomial F)

def generatedPointNormalizedValueTargetRow
    (F : PeriodSearchFamily) :
    CheckedTargetRow (NormalizedValueFields F) :=
  CheckedTargetRow.ofGeneratedPointTargetRow
    (GeneratedPointClosureW11.matrix.normalizedValue F)

def generatedPointLowerBoundTargetRow
    (F : PeriodSearchFamily) :
    CheckedTargetRow (LowerBoundFields F) :=
  CheckedTargetRow.ofGeneratedPointTargetRow
    (GeneratedPointClosureW11.matrix.lowerBound F)

def generatedPointCrossBlockLedgerTargetRow
    (F : PeriodSearchFamily) :
    CheckedTargetRow (CrossBlockInequalityLedger F) :=
  CheckedTargetRow.ofGeneratedPointTargetRow
    (GeneratedPointClosureW11.matrix.crossBlockLedger F)

def flexibleTransitionRouteTargetRow :
    CheckedTargetRow FlexibleTransitionRouteFields :=
  CheckedTargetRow.ofFlexibleStrongTargetRow
    FlexibleTransitionClosureW11.matrix.transitionRouteTargets

def flexibleCandidateAssemblyTargetRow :
    CheckedTargetRow FlexibleCandidateAssemblyFields :=
  CheckedTargetRow.ofFlexibleStrongTargetRow
    FlexibleTransitionClosureW11.matrix.candidateAssemblyTargets

def roleHingeCrossBlockInequalityPackageTargetRow
    (F : RoleHingePeriodSearchFamily) :
    CheckedTargetRow (RoleHingeCrossBlockInequalityPackage F) :=
  CheckedTargetRow.ofExactTarget
    (fun C => C.targetUpperConstructionFiveSixteen)

/-! ## Explicit field-shape ledger -/

/-- Source-facing field shapes consumed by this integrated cross-block layer.
Rows containing the missing numeric inequalities remain visible inputs. -/
structure ExplicitFieldShapes where
  polynomialRows :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  valueRows :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Type
  lengthTwoRows : PeriodSearchFamily -> Prop
  generatedPointTables :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  packedInequalities :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  valueMatrices :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Type
  lowerTables :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  positionPolynomialCertificates :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  positionValueCertificates :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Type
  sqDistanceTables :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  polynomialRowFamilies : PeriodSearchFamily -> Prop
  valueRowFamilies : PeriodSearchFamily -> Type
  valueMatrixFamilies : PeriodSearchFamily -> Type
  lowerTableFamilies : PeriodSearchFamily -> Prop
  inequalityLedgers : PeriodSearchFamily -> Type
  closureLedgers : PeriodSearchFamily -> Type
  normalizedPolynomialFields : PeriodSearchFamily -> Prop
  normalizedValueFields : PeriodSearchFamily -> Type
  lowerBoundFields : PeriodSearchFamily -> Type
  roleHingeInequalityPackages : RoleHingePeriodSearchFamily -> Prop
  flexibleTransitionRouteFields : Type
  flexibleCandidateAssemblyFields : Type

/-- Public list of the explicit field shapes. -/
def explicitFieldShapes : ExplicitFieldShapes where
  polynomialRows := PolynomialRows
  valueRows := ValueRows
  lengthTwoRows := LengthTwoRows
  generatedPointTables := GeneratedPointTable
  packedInequalities := PackedInequalities
  valueMatrices := NonConnectorValueMatrix
  lowerTables := NonConnectorLowerTable
  positionPolynomialCertificates := PositionPolynomialCertificate
  positionValueCertificates := PositionValueCertificate
  sqDistanceTables := SqDistanceTable
  polynomialRowFamilies := PolynomialRowFamilies
  valueRowFamilies := ValueRowFamilies
  valueMatrixFamilies := NonConnectorValueMatrixFamily
  lowerTableFamilies := NonConnectorLowerTableFamily
  inequalityLedgers := CrossBlockInequalityLedger
  closureLedgers := CrossBlockClosureLedger
  normalizedPolynomialFields := NormalizedPolynomialFields
  normalizedValueFields := NormalizedValueFields
  lowerBoundFields := LowerBoundFields
  roleHingeInequalityPackages := RoleHingeCrossBlockInequalityPackage
  flexibleTransitionRouteFields := FlexibleTransitionRouteFields
  flexibleCandidateAssemblyFields := FlexibleCandidateAssemblyFields

/-! ## Integrated matrix -/

/-- The checked W11 integrated cross-block matrix. -/
structure Matrix where
  fields : ExplicitFieldShapes
  generatedPointClosure : GeneratedPointClosureW11.Matrix
  flexibleTransitionClosure : FlexibleTransitionClosureW11.Matrix
  polynomialRows :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockRouteRow F k hk (PolynomialRows F k hk)
  valueRows :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockRouteRow F k hk (ValueRows F k hk)
  generatedPointTables :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockRouteRow F k hk (GeneratedPointTable F k hk)
  packedInequalities :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockRouteRow F k hk (PackedInequalities F k hk)
  valueMatrices :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockRouteRow F k hk (NonConnectorValueMatrix F k hk)
  lowerTables :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockRouteRow F k hk (NonConnectorLowerTable F k hk)
  positionPolynomialCertificates :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockRouteRow F k hk (PositionPolynomialCertificate F k hk)
  positionValueCertificates :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockRouteRow F k hk (PositionValueCertificate F k hk)
  sqDistanceTables :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockRouteRow F k hk (SqDistanceTable F k hk)
  lengthTwoRows :
    forall F : PeriodSearchFamily,
      BlockRouteRow
        F 2 CrossBlockValueSearchW10.twoPositive (LengthTwoRows F)
  polynomialRowFamilies :
    forall F : PeriodSearchFamily,
      FamilyRouteRow F (PolynomialRowFamilies F)
  valueRowFamilies :
    forall F : PeriodSearchFamily,
      FamilyRouteRow F (ValueRowFamilies F)
  valueMatrixFamilies :
    forall F : PeriodSearchFamily,
      FamilyRouteRow F (NonConnectorValueMatrixFamily F)
  lowerTableFamilies :
    forall F : PeriodSearchFamily,
      FamilyRouteRow F (NonConnectorLowerTableFamily F)
  inequalityLedgers :
    forall F : PeriodSearchFamily,
      FamilyRouteRow F (CrossBlockInequalityLedger F)
  closureLedgers :
    forall F : PeriodSearchFamily,
      FamilyRouteRow F (CrossBlockClosureLedger F)
  normalizedPolynomialFields :
    forall F : PeriodSearchFamily,
      FamilyRouteRow F (NormalizedPolynomialFields F)
  normalizedValueFields :
    forall F : PeriodSearchFamily,
      FamilyRouteRow F (NormalizedValueFields F)
  lowerBoundFields :
    forall F : PeriodSearchFamily,
      FamilyRouteRow F (LowerBoundFields F)
  generatedPointNormalizedPolynomialTargets :
    forall F : PeriodSearchFamily,
      CheckedTargetRow (NormalizedPolynomialFields F)
  generatedPointNormalizedValueTargets :
    forall F : PeriodSearchFamily,
      CheckedTargetRow (NormalizedValueFields F)
  generatedPointLowerBoundTargets :
    forall F : PeriodSearchFamily,
      CheckedTargetRow (LowerBoundFields F)
  generatedPointCrossBlockLedgerTargets :
    forall F : PeriodSearchFamily,
      CheckedTargetRow (CrossBlockInequalityLedger F)
  flexibleTransitionRouteTargets :
    CheckedTargetRow FlexibleTransitionRouteFields
  flexibleCandidateAssemblyTargets :
    CheckedTargetRow FlexibleCandidateAssemblyFields
  roleHingeInequalityPackageTargets :
    forall F : RoleHingePeriodSearchFamily,
      CheckedTargetRow (RoleHingeCrossBlockInequalityPackage F)

/-- The integrated W11 cross-block route ledger. -/
def matrix : Matrix where
  fields := explicitFieldShapes
  generatedPointClosure := GeneratedPointClosureW11.matrix
  flexibleTransitionClosure := FlexibleTransitionClosureW11.matrix
  polynomialRows := polynomialRowsBlockRow
  valueRows := valueRowsBlockRow
  generatedPointTables := generatedPointTableBlockRow
  packedInequalities := packedInequalitiesBlockRow
  valueMatrices := valueMatrixBlockRow
  lowerTables := lowerTableBlockRow
  positionPolynomialCertificates := positionPolynomialCertificateBlockRow
  positionValueCertificates := positionValueCertificateBlockRow
  sqDistanceTables := sqDistanceTableBlockRow
  lengthTwoRows := lengthTwoRowsBlockRow
  polynomialRowFamilies := polynomialRowFamiliesRow
  valueRowFamilies := valueRowFamiliesRow
  valueMatrixFamilies := valueMatrixFamilyRow
  lowerTableFamilies := lowerTableFamilyRow
  inequalityLedgers := crossBlockInequalityLedgerRow
  closureLedgers := crossBlockClosureLedgerRow
  normalizedPolynomialFields := normalizedPolynomialFieldsFamilyRow
  normalizedValueFields := normalizedValueFieldsFamilyRow
  lowerBoundFields := lowerBoundFieldsFamilyRow
  generatedPointNormalizedPolynomialTargets :=
    generatedPointNormalizedPolynomialTargetRow
  generatedPointNormalizedValueTargets :=
    generatedPointNormalizedValueTargetRow
  generatedPointLowerBoundTargets := generatedPointLowerBoundTargetRow
  generatedPointCrossBlockLedgerTargets :=
    generatedPointCrossBlockLedgerTargetRow
  flexibleTransitionRouteTargets := flexibleTransitionRouteTargetRow
  flexibleCandidateAssemblyTargets := flexibleCandidateAssemblyTargetRow
  roleHingeInequalityPackageTargets :=
    roleHingeCrossBlockInequalityPackageTargetRow

/-! ## Public projections from integrated rows -/

theorem separated_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  (matrix.inequalityLedgers F).separated L k hk

def closedPlacement_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  (matrix.inequalityLedgers F).closedPlacement L k hk

theorem exactBlockTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.inequalityLedgers F).exactBlockTarget L k hk

theorem targetUpperConstructionFiveSixteen_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.inequalityLedgers F).exactTarget L

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.inequalityLedgers F).fixedTarget L n

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.inequalityLedgers F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteenAt_of_valueRows
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : ValueRows F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.valueRows F k hk).exactBlockTarget R

theorem targetUpperConstructionFiveSixteenAt_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.valueRowFamilies F).fixedTarget R n

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.valueRowFamilies F).arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_normalizedPolynomialFields
    {F : PeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPointNormalizedPolynomialTargets F).exactTarget C

theorem targetUpperConstructionFiveSixteenAt_of_normalizedPolynomialFields
    {F : PeriodSearchFamily}
    (C : NormalizedPolynomialFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.generatedPointNormalizedPolynomialTargets F).fixedTarget C n

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_normalizedPolynomialFields
    {F : PeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointNormalizedPolynomialTargets F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_flexibleTransitionRouteFields
    (R : FlexibleTransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.flexibleTransitionRouteTargets.exactTarget R

theorem targetUpperConstructionFiveSixteenAt_of_flexibleTransitionRouteFields
    (R : FlexibleTransitionRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.flexibleTransitionRouteTargets.fixedTarget R n

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_flexibleTransitionRouteFields
    (R : FlexibleTransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleTransitionRouteTargets.arbitraryTarget R

theorem
    targetUpperConstructionFiveSixteen_of_roleHingeInequalityPackage
    {F : RoleHingePeriodSearchFamily}
    (C : RoleHingeCrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.roleHingeInequalityPackageTargets F).exactTarget C

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_roleHingeInequalityPackage
    {F : RoleHingePeriodSearchFamily}
    (C : RoleHingeCrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.roleHingeInequalityPackageTargets F).arbitraryTarget C

end

end CrossBlockIntegratedW11
end PachToth
end ErdosProblems1066
