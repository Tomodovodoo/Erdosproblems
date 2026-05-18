import ErdosProblems1066.PachToth.CrossBlockIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.GeneratedPointIntegratedMatrixW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix
import ErdosProblems1066.PachToth.GeneratedTargetIntegratedW11

set_option autoImplicit false

/-!
# W11 cross-block target integration

This file is a target-facing adapter over the W11 cross-block rows.  It keeps
the polynomial, value, and ledger input packages visible, and records only
checked projections from those packages to the Pach--Toth target forms.

Fixed-period rows project to the exact block target at `16 * k`.  Family and
ledger rows additionally project through the checked arbitrary-`n` route.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockTargetIntegratedW11

noncomputable section

universe u

abbrev PeriodSearchFamily :=
  CrossBlockIntegratedW11.PeriodSearchFamily

abbrev RoleHingePeriodSearchFamily :=
  CrossBlockIntegratedW11.RoleHingePeriodSearchFamily

abbrev GeneratedGlobalSeparationAt
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) : Prop :=
  CrossBlockIntegratedW11.GeneratedGlobalSeparationAt F k hk

abbrev CrossBlockClosureLedger (F : PeriodSearchFamily) :=
  CrossBlockIntegratedW11.CrossBlockClosureLedger F

abbrev CrossBlockInequalityLedger (F : PeriodSearchFamily) :=
  CrossBlockIntegratedW11.CrossBlockInequalityLedger F

abbrev PolynomialRows (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockIntegratedW11.PolynomialRows F k hk

abbrev ValueRows (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockIntegratedW11.ValueRows F k hk

abbrev PolynomialRowFamilies (F : PeriodSearchFamily) :=
  CrossBlockIntegratedW11.PolynomialRowFamilies F

abbrev ValueRowFamilies (F : PeriodSearchFamily) :=
  CrossBlockIntegratedW11.ValueRowFamilies F

abbrev GeneratedPointTable (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockIntegratedW11.GeneratedPointTable F k hk

abbrev PackedInequalities (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockIntegratedW11.PackedInequalities F k hk

abbrev NonConnectorValueMatrix
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockIntegratedW11.NonConnectorValueMatrix F k hk

abbrev NonConnectorLowerTable
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockIntegratedW11.NonConnectorLowerTable F k hk

abbrev PositionPolynomialCertificate
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockIntegratedW11.PositionPolynomialCertificate F k hk

abbrev PositionValueCertificate
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockIntegratedW11.PositionValueCertificate F k hk

abbrev SqDistanceTable
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockIntegratedW11.SqDistanceTable F k hk

abbrev NonConnectorValueMatrixFamily (F : PeriodSearchFamily) :=
  CrossBlockIntegratedW11.NonConnectorValueMatrixFamily F

abbrev NonConnectorLowerTableFamily (F : PeriodSearchFamily) :=
  CrossBlockIntegratedW11.NonConnectorLowerTableFamily F

abbrev RoleHingeCrossBlockInequalityPackage
    (F : RoleHingePeriodSearchFamily) :=
  CrossBlockIntegratedW11.RoleHingeCrossBlockInequalityPackage F

abbrev BlockRouteRow
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k)
    (alpha : Sort u) :=
  CrossBlockIntegratedW11.BlockRouteRow F k hk alpha

abbrev FamilyRouteRow (F : PeriodSearchFamily) (alpha : Sort u) :=
  CrossBlockIntegratedW11.FamilyRouteRow F alpha

abbrev CheckedTargetRow (alpha : Sort u) :=
  CrossBlockIntegratedW11.CheckedTargetRow alpha

abbrev TargetRoute (alpha : Sort u) :=
  GeneratedTargetIntegratedW11.TargetRoute alpha

abbrev ArbitraryNTargetFacade :=
  GeneratedTargetIntegratedW11.ArbitraryNTargetFacade

/-! ## Generic target rows -/

/-- Reuse a checked cross-block target row as a target-facing route. -/
def targetRouteOfCheckedTargetRow
    {alpha : Sort u}
    (R : CheckedTargetRow alpha) :
    TargetRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := fun a =>
    GeneratedTargetIntegratedW11.TargetRoute.eventualTargetOfArbitrary
      (R.arbitraryTarget a)
  arbitraryTarget := R.arbitraryTarget
  targetFacade := fun a =>
    { fixedTarget := R.fixedTarget a
      arbitraryTarget := R.arbitraryTarget a }

/-- A fixed-period cross-block row.  Such a row gives the exact target for
the displayed block count `16 * k`. -/
structure BlockTargetRoute
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k)
    (alpha : Sort u) : Sort (max 1 u) where
  separated : alpha -> GeneratedGlobalSeparationAt F k hk
  closedPlacement :
    alpha -> DeformedPlacement.ClosedPlacement k hk
  exactBlockTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenAt (16 * k)

namespace BlockTargetRoute

/-- Convert an integrated fixed-period row to its target-facing view. -/
def ofIntegratedRow
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    {alpha : Sort u}
    (R : BlockRouteRow F k hk alpha) :
    BlockTargetRoute F k hk alpha where
  separated := R.separated
  closedPlacement := R.closedPlacement
  exactBlockTarget := R.exactBlockTarget

end BlockTargetRoute

/-- A cross-block family row.  Family rows carry all positive block counts
and therefore route to exact, fixed-`n`, eventual, arbitrary, and facade
forms. -/
structure FamilyTargetRoute
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
  route : TargetRoute alpha

namespace FamilyTargetRoute

/-- Convert an integrated family row to its target-facing view. -/
def ofIntegratedRow
    {F : PeriodSearchFamily} {alpha : Sort u}
    (R : FamilyRouteRow F alpha) :
    FamilyTargetRoute F alpha where
  separated := R.separated
  closedPlacement := R.closedPlacement
  exactBlockTarget := R.exactBlockTarget
  route := targetRouteOfCheckedTargetRow R.checkedTargets

end FamilyTargetRoute

/-! ## Explicit input shapes -/

/-- Polynomial-style cross-block packages still supplied by external rows. -/
structure PolynomialInputFields where
  rows :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  rowFamilies : PeriodSearchFamily -> Prop
  generatedPointTables :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  packedInequalities :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  positionCertificates :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop

/-- Value-style cross-block packages still supplied by external rows. -/
structure ValueInputFields where
  rows :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Type
  rowFamilies : PeriodSearchFamily -> Type
  valueMatrices :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Type
  valueMatrixFamilies : PeriodSearchFamily -> Type
  lowerTables :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  lowerTableFamilies : PeriodSearchFamily -> Prop
  positionCertificates :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Type
  sqDistanceTables :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop

/-- Ledger-style cross-block packages still supplied by external rows. -/
structure LedgerInputFields where
  inequalityLedgers : PeriodSearchFamily -> Type
  closureLedgers : PeriodSearchFamily -> Type
  roleHingeInequalityPackages : RoleHingePeriodSearchFamily -> Prop

/-- Public input ledger for the target-facing cross-block matrix. -/
structure ExplicitCrossBlockTargetInputs where
  sourceFieldShapes : CrossBlockIntegratedW11.ExplicitFieldShapes
  polynomial : PolynomialInputFields
  value : ValueInputFields
  ledger : LedgerInputFields

def polynomialInputFields : PolynomialInputFields where
  rows := PolynomialRows
  rowFamilies := PolynomialRowFamilies
  generatedPointTables := GeneratedPointTable
  packedInequalities := PackedInequalities
  positionCertificates := PositionPolynomialCertificate

def valueInputFields : ValueInputFields where
  rows := ValueRows
  rowFamilies := ValueRowFamilies
  valueMatrices := NonConnectorValueMatrix
  valueMatrixFamilies := NonConnectorValueMatrixFamily
  lowerTables := NonConnectorLowerTable
  lowerTableFamilies := NonConnectorLowerTableFamily
  positionCertificates := PositionValueCertificate
  sqDistanceTables := SqDistanceTable

def ledgerInputFields : LedgerInputFields where
  inequalityLedgers := CrossBlockInequalityLedger
  closureLedgers := CrossBlockClosureLedger
  roleHingeInequalityPackages := RoleHingeCrossBlockInequalityPackage

/-- The explicit input packages consumed by this target adapter. -/
def explicitCrossBlockTargetInputs : ExplicitCrossBlockTargetInputs where
  sourceFieldShapes := CrossBlockIntegratedW11.explicitFieldShapes
  polynomial := polynomialInputFields
  value := valueInputFields
  ledger := ledgerInputFields

/-! ## Target row groups -/

/-- Target-facing polynomial row routes. -/
structure PolynomialTargetRows where
  rows :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockTargetRoute F k hk (PolynomialRows F k hk)
  rowFamilies :
    forall F : PeriodSearchFamily,
      FamilyTargetRoute F (PolynomialRowFamilies F)
  generatedPointTables :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockTargetRoute F k hk (GeneratedPointTable F k hk)
  packedInequalities :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockTargetRoute F k hk (PackedInequalities F k hk)
  positionCertificates :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockTargetRoute F k hk (PositionPolynomialCertificate F k hk)

def polynomialTargetRows : PolynomialTargetRows where
  rows := fun F k hk =>
    BlockTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.polynomialRows F k hk)
  rowFamilies := fun F =>
    FamilyTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.polynomialRowFamilies F)
  generatedPointTables := fun F k hk =>
    BlockTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.generatedPointTables F k hk)
  packedInequalities := fun F k hk =>
    BlockTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.packedInequalities F k hk)
  positionCertificates := fun F k hk =>
    BlockTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.positionPolynomialCertificates F k hk)

/-- Target-facing value row routes. -/
structure ValueTargetRows where
  rows :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockTargetRoute F k hk (ValueRows F k hk)
  rowFamilies :
    forall F : PeriodSearchFamily,
      FamilyTargetRoute F (ValueRowFamilies F)
  valueMatrices :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockTargetRoute F k hk (NonConnectorValueMatrix F k hk)
  valueMatrixFamilies :
    forall F : PeriodSearchFamily,
      FamilyTargetRoute F (NonConnectorValueMatrixFamily F)
  lowerTables :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockTargetRoute F k hk (NonConnectorLowerTable F k hk)
  lowerTableFamilies :
    forall F : PeriodSearchFamily,
      FamilyTargetRoute F (NonConnectorLowerTableFamily F)
  positionCertificates :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockTargetRoute F k hk (PositionValueCertificate F k hk)
  sqDistanceTables :
    forall (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k),
      BlockTargetRoute F k hk (SqDistanceTable F k hk)

def valueTargetRows : ValueTargetRows where
  rows := fun F k hk =>
    BlockTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.valueRows F k hk)
  rowFamilies := fun F =>
    FamilyTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.valueRowFamilies F)
  valueMatrices := fun F k hk =>
    BlockTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.valueMatrices F k hk)
  valueMatrixFamilies := fun F =>
    FamilyTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.valueMatrixFamilies F)
  lowerTables := fun F k hk =>
    BlockTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.lowerTables F k hk)
  lowerTableFamilies := fun F =>
    FamilyTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.lowerTableFamilies F)
  positionCertificates := fun F k hk =>
    BlockTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.positionValueCertificates F k hk)
  sqDistanceTables := fun F k hk =>
    BlockTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.sqDistanceTables F k hk)

def generatedTargetCrossBlockLedgerRoute
    (F : PeriodSearchFamily) :
    TargetRoute (CrossBlockInequalityLedger F) :=
  (GeneratedTargetIntegratedW11.matrix.generatedPoint.crossBlockLedger F).route

def pachTothIntegratedCrossBlockClosureRoute
    (F : PeriodSearchFamily) :
    TargetRoute (CrossBlockClosureLedger F) :=
  GeneratedTargetIntegratedW11.TargetRoute.ofExactAndArbitrary
    (fun C =>
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
        C)
    (fun C =>
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
        C)

/-- Target-facing ledger routes. -/
structure LedgerTargetRows where
  inequalityLedgers :
    forall F : PeriodSearchFamily,
      FamilyTargetRoute F (CrossBlockInequalityLedger F)
  closureLedgers :
    forall F : PeriodSearchFamily,
      FamilyTargetRoute F (CrossBlockClosureLedger F)
  generatedTargetInequalityLedgers :
    forall F : PeriodSearchFamily,
      TargetRoute (CrossBlockInequalityLedger F)
  pachTothIntegratedClosureLedgers :
    forall F : PeriodSearchFamily,
      TargetRoute (CrossBlockClosureLedger F)
  roleHingeInequalityPackages :
    forall F : RoleHingePeriodSearchFamily,
      TargetRoute (RoleHingeCrossBlockInequalityPackage F)

def roleHingeInequalityPackageRoute
    (F : RoleHingePeriodSearchFamily) :
    TargetRoute (RoleHingeCrossBlockInequalityPackage F) :=
  targetRouteOfCheckedTargetRow
    (CrossBlockIntegratedW11.matrix.roleHingeInequalityPackageTargets F)

def ledgerTargetRows : LedgerTargetRows where
  inequalityLedgers := fun F =>
    FamilyTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.inequalityLedgers F)
  closureLedgers := fun F =>
    FamilyTargetRoute.ofIntegratedRow
      (CrossBlockIntegratedW11.matrix.closureLedgers F)
  generatedTargetInequalityLedgers :=
    generatedTargetCrossBlockLedgerRoute
  pachTothIntegratedClosureLedgers :=
    pachTothIntegratedCrossBlockClosureRoute
  roleHingeInequalityPackages := roleHingeInequalityPackageRoute

/-! ## Imported checked ledgers -/

/-- Existing W11 ledgers used by this target-facing cross-block adapter. -/
structure ImportedCrossBlockLedgers where
  crossBlockIntegrated : CrossBlockIntegratedW11.Matrix
  crossBlockClosureRoutes :
    forall F : PeriodSearchFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  generatedPointIntegrated : GeneratedPointIntegratedMatrixW11.Matrix
  pachTothIntegrated : PachTothW11IntegratedMatrix.Matrix
  generatedTargetIntegrated : GeneratedTargetIntegratedW11.Matrix

/-- Checked W11 ledgers imported by this file. -/
def importedCrossBlockLedgers : ImportedCrossBlockLedgers where
  crossBlockIntegrated := CrossBlockIntegratedW11.matrix
  crossBlockClosureRoutes :=
    CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  generatedPointIntegrated := GeneratedPointIntegratedMatrixW11.matrix
  pachTothIntegrated := PachTothW11IntegratedMatrix.matrix
  generatedTargetIntegrated := GeneratedTargetIntegratedW11.matrix

/-! ## Integrated target matrix -/

/-- Target-facing W11 cross-block matrix.

The matrix stores route rows only.  Each public target projection below remains
conditional on one of the explicit input packages in `requiredInputs`.
-/
structure Matrix where
  requiredInputs : ExplicitCrossBlockTargetInputs
  importedLedgers : ImportedCrossBlockLedgers
  polynomialRows : PolynomialTargetRows
  valueRows : ValueTargetRows
  ledgerRows : LedgerTargetRows

/-- The checked target-facing cross-block integration matrix. -/
def matrix : Matrix where
  requiredInputs := explicitCrossBlockTargetInputs
  importedLedgers := importedCrossBlockLedgers
  polynomialRows := polynomialTargetRows
  valueRows := valueTargetRows
  ledgerRows := ledgerTargetRows

/-! ## Public conditional projections: polynomial rows -/

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_polynomialRows
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : PolynomialRows F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.polynomialRows.rows F k hk).exactBlockTarget R

theorem targetUpperConstructionFiveSixteen_of_polynomialRowFamilies
    {F : PeriodSearchFamily}
    (R : PolynomialRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.polynomialRows.rowFamilies F).route.exactTarget R

theorem targetUpperConstructionFiveSixteenAt_of_polynomialRowFamilies
    {F : PeriodSearchFamily}
    (R : PolynomialRowFamilies F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.polynomialRows.rowFamilies F).route.fixedTarget R n

theorem targetUpperConstructionFiveSixteenArbitrary_of_polynomialRowFamilies
    {F : PeriodSearchFamily}
    (R : PolynomialRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.polynomialRows.rowFamilies F).route.arbitraryTarget R

theorem targetFacade_of_polynomialRowFamilies
    {F : PeriodSearchFamily}
    (R : PolynomialRowFamilies F) :
    ArbitraryNTargetFacade :=
  (matrix.polynomialRows.rowFamilies F).route.targetFacade R

/-! ## Public conditional projections: value rows -/

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_valueRows
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : ValueRows F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.valueRows.rows F k hk).exactBlockTarget R

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_valueMatrices
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : NonConnectorValueMatrix F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.valueRows.valueMatrices F k hk).exactBlockTarget R

theorem targetUpperConstructionFiveSixteen_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.valueRows.rowFamilies F).route.exactTarget R

theorem targetUpperConstructionFiveSixteenAt_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.valueRows.rowFamilies F).route.fixedTarget R n

theorem targetUpperConstructionFiveSixteenArbitrary_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.valueRows.rowFamilies F).route.arbitraryTarget R

theorem targetFacade_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) :
    ArbitraryNTargetFacade :=
  (matrix.valueRows.rowFamilies F).route.targetFacade R

theorem targetUpperConstructionFiveSixteenArbitrary_of_valueMatrixFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorValueMatrixFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.valueRows.valueMatrixFamilies F).route.arbitraryTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_lowerTableFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.valueRows.lowerTableFamilies F).route.arbitraryTarget R

/-! ## Public conditional projections: ledger rows -/

theorem separated_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  (matrix.ledgerRows.inequalityLedgers F).separated L k hk

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.ledgerRows.inequalityLedgers F).exactBlockTarget L k hk

theorem targetUpperConstructionFiveSixteen_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.ledgerRows.inequalityLedgers F).route.exactTarget L

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.ledgerRows.inequalityLedgers F).route.fixedTarget L n

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledgerRows.inequalityLedgers F).route.arbitraryTarget L

theorem targetFacade_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.ledgerRows.generatedTargetInequalityLedgers F).targetFacade L

theorem
    targetUpperConstructionFiveSixteenArbitrary_viaGeneratedTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledgerRows.generatedTargetInequalityLedgers F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.ledgerRows.closureLedgers F).route.exactTarget C

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.ledgerRows.closureLedgers F).route.fixedTarget C n

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledgerRows.closureLedgers F).route.arbitraryTarget C

theorem
    targetUpperConstructionFiveSixteenArbitrary_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledgerRows.pachTothIntegratedClosureLedgers F).arbitraryTarget C

theorem targetFacade_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.ledgerRows.closureLedgers F).route.targetFacade C

theorem targetUpperConstructionFiveSixteen_of_roleHingeInequalityPackage
    {F : RoleHingePeriodSearchFamily}
    (C : RoleHingeCrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.ledgerRows.roleHingeInequalityPackages F).exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_roleHingeInequalityPackage
    {F : RoleHingePeriodSearchFamily}
    (C : RoleHingeCrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledgerRows.roleHingeInequalityPackages F).arbitraryTarget C

end

end CrossBlockTargetIntegratedW11
end PachToth
end ErdosProblems1066
