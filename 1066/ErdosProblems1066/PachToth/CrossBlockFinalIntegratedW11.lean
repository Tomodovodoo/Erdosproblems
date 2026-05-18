import ErdosProblems1066.PachToth.CrossBlockTargetIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.GeneratedTargetIntegratedW11

set_option autoImplicit false

/-!
# W11 final cross-block aggregate matrix

This file is the final target-facing aggregate for the W11 cross-block rows.
It keeps the polynomial, value, and ledger input packages explicit, imports
the checked source and target matrices, and exposes Pach--Toth conclusions
only after one of those packages is supplied.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockFinalIntegratedW11

noncomputable section

universe u

abbrev PeriodSearchFamily :=
  CrossBlockTargetIntegratedW11.PeriodSearchFamily

abbrev RoleHingePeriodSearchFamily :=
  CrossBlockTargetIntegratedW11.RoleHingePeriodSearchFamily

abbrev GeneratedGlobalSeparationAt
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) : Prop :=
  CrossBlockTargetIntegratedW11.GeneratedGlobalSeparationAt F k hk

abbrev CrossBlockInequalityLedger (F : PeriodSearchFamily) :=
  CrossBlockTargetIntegratedW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger (F : PeriodSearchFamily) :=
  CrossBlockTargetIntegratedW11.CrossBlockClosureLedger F

abbrev PolynomialRows
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.PolynomialRows F k hk

abbrev PolynomialRowFamilies (F : PeriodSearchFamily) :=
  CrossBlockTargetIntegratedW11.PolynomialRowFamilies F

abbrev GeneratedPointTable
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.GeneratedPointTable F k hk

abbrev PackedInequalities
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.PackedInequalities F k hk

abbrev PositionPolynomialCertificate
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.PositionPolynomialCertificate F k hk

abbrev ValueRows
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.ValueRows F k hk

abbrev ValueRowFamilies (F : PeriodSearchFamily) :=
  CrossBlockTargetIntegratedW11.ValueRowFamilies F

abbrev NonConnectorValueMatrix
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.NonConnectorValueMatrix F k hk

abbrev NonConnectorValueMatrixFamily (F : PeriodSearchFamily) :=
  CrossBlockTargetIntegratedW11.NonConnectorValueMatrixFamily F

abbrev NonConnectorLowerTable
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.NonConnectorLowerTable F k hk

abbrev NonConnectorLowerTableFamily (F : PeriodSearchFamily) :=
  CrossBlockTargetIntegratedW11.NonConnectorLowerTableFamily F

abbrev PositionValueCertificate
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.PositionValueCertificate F k hk

abbrev SqDistanceTable
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.SqDistanceTable F k hk

abbrev RoleHingeCrossBlockInequalityPackage
    (F : RoleHingePeriodSearchFamily) :=
  CrossBlockTargetIntegratedW11.RoleHingeCrossBlockInequalityPackage F

abbrev BlockTargetRoute
    (F : PeriodSearchFamily) (k : Nat) (hk : 0 < k)
    (alpha : Sort u) :=
  CrossBlockTargetIntegratedW11.BlockTargetRoute F k hk alpha

abbrev FamilyTargetRoute
    (F : PeriodSearchFamily) (alpha : Sort u) :=
  CrossBlockTargetIntegratedW11.FamilyTargetRoute F alpha

abbrev TargetRoute (alpha : Sort u) :=
  GeneratedTargetIntegratedW11.TargetRoute alpha

abbrev ArbitraryNTargetFacade :=
  GeneratedTargetIntegratedW11.ArbitraryNTargetFacade

/-! ## Shared final route shape -/

/-- Exact, fixed-`n`, eventual, arbitrary, and facade projections from one
explicit cross-block package. -/
structure ConditionalPachTothRoute (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

namespace ConditionalPachTothRoute

/-- Reuse a generated target route as a final conditional route. -/
def ofTargetRoute
    {alpha : Sort u}
    (R : TargetRoute alpha) :
    ConditionalPachTothRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

/-- Forget the separation fields of a cross-block family route. -/
def ofFamilyTargetRoute
    {F : PeriodSearchFamily} {alpha : Sort u}
    (R : FamilyTargetRoute F alpha) :
    ConditionalPachTothRoute alpha :=
  ofTargetRoute R.route

end ConditionalPachTothRoute

/-! ## Explicit input fields -/

/-- Polynomial-style cross-block input package shapes. -/
structure ExplicitPolynomialFields where
  rows :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  rowFamilies : PeriodSearchFamily -> Prop
  generatedPointTables :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  packedInequalities :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop
  positionCertificates :
    forall (_F : PeriodSearchFamily) (k : Nat), 0 < k -> Prop

/-- Value-style cross-block input package shapes. -/
structure ExplicitValueFields where
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

/-- Ledger-style cross-block input package shapes. -/
structure ExplicitLedgerFields where
  inequalityLedgers : PeriodSearchFamily -> Type
  closureLedgers : PeriodSearchFamily -> Type
  roleHingeInequalityPackages : RoleHingePeriodSearchFamily -> Prop

/-- All explicit cross-block input shapes consumed by the final aggregate. -/
structure ExplicitCrossBlockFields where
  polynomial : ExplicitPolynomialFields
  value : ExplicitValueFields
  ledger : ExplicitLedgerFields
  targetInputs : CrossBlockTargetIntegratedW11.ExplicitCrossBlockTargetInputs
  sourceFieldShapes : CrossBlockIntegratedW11.ExplicitFieldShapes

def explicitPolynomialFields : ExplicitPolynomialFields where
  rows := PolynomialRows
  rowFamilies := PolynomialRowFamilies
  generatedPointTables := GeneratedPointTable
  packedInequalities := PackedInequalities
  positionCertificates := PositionPolynomialCertificate

def explicitValueFields : ExplicitValueFields where
  rows := ValueRows
  rowFamilies := ValueRowFamilies
  valueMatrices := NonConnectorValueMatrix
  valueMatrixFamilies := NonConnectorValueMatrixFamily
  lowerTables := NonConnectorLowerTable
  lowerTableFamilies := NonConnectorLowerTableFamily
  positionCertificates := PositionValueCertificate
  sqDistanceTables := SqDistanceTable

def explicitLedgerFields : ExplicitLedgerFields where
  inequalityLedgers := CrossBlockInequalityLedger
  closureLedgers := CrossBlockClosureLedger
  roleHingeInequalityPackages := RoleHingeCrossBlockInequalityPackage

/-- Public ledger of every explicit package shape. -/
def explicitCrossBlockFields : ExplicitCrossBlockFields where
  polynomial := explicitPolynomialFields
  value := explicitValueFields
  ledger := explicitLedgerFields
  targetInputs := CrossBlockTargetIntegratedW11.explicitCrossBlockTargetInputs
  sourceFieldShapes := CrossBlockIntegratedW11.explicitFieldShapes

/-! ## Imported checked matrices -/

/-- Checked matrices used by the final cross-block aggregate. -/
structure ImportedMatrices where
  targetIntegrated : CrossBlockTargetIntegratedW11.Matrix
  sourceIntegrated : CrossBlockIntegratedW11.Matrix
  inequalityClosure :
    forall F : PeriodSearchFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  generatedTarget : GeneratedTargetIntegratedW11.Matrix

def importedMatrices : ImportedMatrices where
  targetIntegrated := CrossBlockTargetIntegratedW11.matrix
  sourceIntegrated := CrossBlockIntegratedW11.matrix
  inequalityClosure := CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  generatedTarget := GeneratedTargetIntegratedW11.matrix

/-! ## Final route groups -/

/-- Final polynomial route rows. -/
structure PolynomialRoutes where
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

def polynomialRoutes : PolynomialRoutes where
  rows := CrossBlockTargetIntegratedW11.matrix.polynomialRows.rows
  rowFamilies := CrossBlockTargetIntegratedW11.matrix.polynomialRows.rowFamilies
  generatedPointTables :=
    CrossBlockTargetIntegratedW11.matrix.polynomialRows.generatedPointTables
  packedInequalities :=
    CrossBlockTargetIntegratedW11.matrix.polynomialRows.packedInequalities
  positionCertificates :=
    CrossBlockTargetIntegratedW11.matrix.polynomialRows.positionCertificates

/-- Final value route rows. -/
structure ValueRoutes where
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

def valueRoutes : ValueRoutes where
  rows := CrossBlockTargetIntegratedW11.matrix.valueRows.rows
  rowFamilies := CrossBlockTargetIntegratedW11.matrix.valueRows.rowFamilies
  valueMatrices := CrossBlockTargetIntegratedW11.matrix.valueRows.valueMatrices
  valueMatrixFamilies :=
    CrossBlockTargetIntegratedW11.matrix.valueRows.valueMatrixFamilies
  lowerTables := CrossBlockTargetIntegratedW11.matrix.valueRows.lowerTables
  lowerTableFamilies :=
    CrossBlockTargetIntegratedW11.matrix.valueRows.lowerTableFamilies
  positionCertificates :=
    CrossBlockTargetIntegratedW11.matrix.valueRows.positionCertificates
  sqDistanceTables := CrossBlockTargetIntegratedW11.matrix.valueRows.sqDistanceTables

/-- Final ledger routes. -/
structure LedgerRoutes where
  inequalityLedgers :
    forall F : PeriodSearchFamily,
      FamilyTargetRoute F (CrossBlockInequalityLedger F)
  closureLedgers :
    forall F : PeriodSearchFamily,
      FamilyTargetRoute F (CrossBlockClosureLedger F)
  generatedTargetInequalityLedgers :
    forall F : PeriodSearchFamily,
      ConditionalPachTothRoute (CrossBlockInequalityLedger F)
  pachTothIntegratedClosureLedgers :
    forall F : PeriodSearchFamily,
      ConditionalPachTothRoute (CrossBlockClosureLedger F)
  roleHingeInequalityPackages :
    forall F : RoleHingePeriodSearchFamily,
      ConditionalPachTothRoute (RoleHingeCrossBlockInequalityPackage F)

def ledgerRoutes : LedgerRoutes where
  inequalityLedgers :=
    CrossBlockTargetIntegratedW11.matrix.ledgerRows.inequalityLedgers
  closureLedgers :=
    CrossBlockTargetIntegratedW11.matrix.ledgerRows.closureLedgers
  generatedTargetInequalityLedgers := fun F =>
    ConditionalPachTothRoute.ofTargetRoute
      (CrossBlockTargetIntegratedW11.matrix.ledgerRows
        |>.generatedTargetInequalityLedgers F)
  pachTothIntegratedClosureLedgers := fun F =>
    ConditionalPachTothRoute.ofTargetRoute
      (CrossBlockTargetIntegratedW11.matrix.ledgerRows
        |>.pachTothIntegratedClosureLedgers F)
  roleHingeInequalityPackages := fun F =>
    ConditionalPachTothRoute.ofTargetRoute
      (CrossBlockTargetIntegratedW11.matrix.ledgerRows
        |>.roleHingeInequalityPackages F)

/-! ## Final aggregate matrix -/

/-- Final W11 cross-block aggregate matrix.

The matrix contains route ledgers and package shapes only.  All public target
statements below remain conditional on one explicit input package.
-/
structure Matrix where
  fields : ExplicitCrossBlockFields
  imported : ImportedMatrices
  polynomial : PolynomialRoutes
  value : ValueRoutes
  ledger : LedgerRoutes

/-- The checked final W11 cross-block aggregate. -/
def matrix : Matrix where
  fields := explicitCrossBlockFields
  imported := importedMatrices
  polynomial := polynomialRoutes
  value := valueRoutes
  ledger := ledgerRoutes

/-! ## Polynomial projections -/

theorem exactBlockTarget_of_polynomialRows
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : PolynomialRows F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.polynomial.rows F k hk).exactBlockTarget R

theorem exactBlockTarget_of_generatedPointTables
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : GeneratedPointTable F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.polynomial.generatedPointTables F k hk).exactBlockTarget R

theorem exactBlockTarget_of_packedInequalities
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : PackedInequalities F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.polynomial.packedInequalities F k hk).exactBlockTarget R

theorem exactBlockTarget_of_positionPolynomialCertificates
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : PositionPolynomialCertificate F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.polynomial.positionCertificates F k hk).exactBlockTarget R

theorem exactTarget_of_polynomialRowFamilies
    {F : PeriodSearchFamily}
    (R : PolynomialRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.polynomial.rowFamilies F).route.exactTarget R

theorem fixedTarget_of_polynomialRowFamilies
    {F : PeriodSearchFamily}
    (R : PolynomialRowFamilies F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.polynomial.rowFamilies F).route.fixedTarget R n

theorem eventualTarget_of_polynomialRowFamilies
    {F : PeriodSearchFamily}
    (R : PolynomialRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.polynomial.rowFamilies F).route.eventualTarget R

theorem arbitraryTarget_of_polynomialRowFamilies
    {F : PeriodSearchFamily}
    (R : PolynomialRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.polynomial.rowFamilies F).route.arbitraryTarget R

theorem targetFacade_of_polynomialRowFamilies
    {F : PeriodSearchFamily}
    (R : PolynomialRowFamilies F) :
    ArbitraryNTargetFacade :=
  (matrix.polynomial.rowFamilies F).route.targetFacade R

/-! ## Value projections -/

theorem exactBlockTarget_of_valueRows
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : ValueRows F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.value.rows F k hk).exactBlockTarget R

theorem exactBlockTarget_of_valueMatrices
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : NonConnectorValueMatrix F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.value.valueMatrices F k hk).exactBlockTarget R

theorem exactBlockTarget_of_lowerTables
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : NonConnectorLowerTable F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.value.lowerTables F k hk).exactBlockTarget R

theorem exactBlockTarget_of_positionValueCertificates
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : PositionValueCertificate F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.value.positionCertificates F k hk).exactBlockTarget R

theorem exactBlockTarget_of_sqDistanceTables
    {F : PeriodSearchFamily} {k : Nat} {hk : 0 < k}
    (R : SqDistanceTable F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.value.sqDistanceTables F k hk).exactBlockTarget R

theorem exactTarget_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.value.rowFamilies F).route.exactTarget R

theorem fixedTarget_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.value.rowFamilies F).route.fixedTarget R n

theorem eventualTarget_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.value.rowFamilies F).route.eventualTarget R

theorem arbitraryTarget_of_valueRowFamilies
    {F : PeriodSearchFamily}
    (R : ValueRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.value.rowFamilies F).route.arbitraryTarget R

theorem exactTarget_of_valueMatrixFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorValueMatrixFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.value.valueMatrixFamilies F).route.exactTarget R

theorem fixedTarget_of_valueMatrixFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorValueMatrixFamily F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.value.valueMatrixFamilies F).route.fixedTarget R n

theorem eventualTarget_of_valueMatrixFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorValueMatrixFamily F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.value.valueMatrixFamilies F).route.eventualTarget R

theorem arbitraryTarget_of_valueMatrixFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorValueMatrixFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.value.valueMatrixFamilies F).route.arbitraryTarget R

theorem exactTarget_of_lowerTableFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.value.lowerTableFamilies F).route.exactTarget R

theorem fixedTarget_of_lowerTableFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorLowerTableFamily F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.value.lowerTableFamilies F).route.fixedTarget R n

theorem eventualTarget_of_lowerTableFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.value.lowerTableFamilies F).route.eventualTarget R

theorem arbitraryTarget_of_lowerTableFamilies
    {F : PeriodSearchFamily}
    (R : NonConnectorLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.value.lowerTableFamilies F).route.arbitraryTarget R

/-! ## Ledger projections -/

theorem separated_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  (matrix.ledger.inequalityLedgers F).separated L k hk

theorem exactBlockTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.ledger.inequalityLedgers F).exactBlockTarget L k hk

theorem exactTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.ledger.inequalityLedgers F).route.exactTarget L

theorem fixedTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.ledger.inequalityLedgers F).route.fixedTarget L n

theorem eventualTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.ledger.inequalityLedgers F).route.eventualTarget L

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledger.inequalityLedgers F).route.arbitraryTarget L

theorem exactTarget_viaGeneratedTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.ledger.generatedTargetInequalityLedgers F).exactTarget L

theorem fixedTarget_viaGeneratedTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.ledger.generatedTargetInequalityLedgers F).fixedTarget L n

theorem eventualTarget_viaGeneratedTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.ledger.generatedTargetInequalityLedgers F).eventualTarget L

theorem arbitraryTarget_viaGeneratedTarget_of_crossBlockInequalityLedger
    {F : PeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledger.generatedTargetInequalityLedgers F).arbitraryTarget L

theorem separated_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  (matrix.ledger.closureLedgers F).separated C k hk

theorem exactBlockTarget_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.ledger.closureLedgers F).exactBlockTarget C k hk

theorem exactTarget_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.ledger.closureLedgers F).route.exactTarget C

theorem fixedTarget_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.ledger.closureLedgers F).route.fixedTarget C n

theorem eventualTarget_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.ledger.closureLedgers F).route.eventualTarget C

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledger.closureLedgers F).route.arbitraryTarget C

theorem exactTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.ledger.pachTothIntegratedClosureLedgers F).exactTarget C

theorem fixedTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.ledger.pachTothIntegratedClosureLedgers F).fixedTarget C n

theorem eventualTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.ledger.pachTothIntegratedClosureLedgers F).eventualTarget C

theorem arbitraryTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : PeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledger.pachTothIntegratedClosureLedgers F).arbitraryTarget C

theorem exactTarget_of_roleHingeInequalityPackage
    {F : RoleHingePeriodSearchFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.ledger.roleHingeInequalityPackages F).exactTarget R

theorem fixedTarget_of_roleHingeInequalityPackage
    {F : RoleHingePeriodSearchFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.ledger.roleHingeInequalityPackages F).fixedTarget R n

theorem eventualTarget_of_roleHingeInequalityPackage
    {F : RoleHingePeriodSearchFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.ledger.roleHingeInequalityPackages F).eventualTarget R

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : RoleHingePeriodSearchFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.ledger.roleHingeInequalityPackages F).arbitraryTarget R

end

end CrossBlockFinalIntegratedW11
end PachToth
end ErdosProblems1066
