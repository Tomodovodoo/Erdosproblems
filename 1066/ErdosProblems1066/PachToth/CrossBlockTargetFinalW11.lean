import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockTargetIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency
import ErdosProblems1066.PachToth.GeneratedTargetFinalW11
import ErdosProblems1066.PachToth.ArbitraryNTargetFinalW11

set_option autoImplicit false

/-!
# W11 final cross-block target consistency

This file is the final target-facing consistency layer for the W11 cross-block
rows present in this checkout.  It keeps the polynomial, value, and ledger
packages visible, records the checked adjacent final layers, and exposes only
conditional projections from explicit inputs.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockTargetFinalW11

noncomputable section

universe u

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev CrossBlockFamily :=
  CrossBlockFinalIntegratedW11.PeriodSearchFamily

abbrev RoleHingeCrossBlockFamily :=
  CrossBlockFinalIntegratedW11.RoleHingePeriodSearchFamily

abbrev GeneratedGlobalSeparationAt
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) : Prop :=
  CrossBlockFinalIntegratedW11.GeneratedGlobalSeparationAt F k hk

abbrev ArbitraryNTargetFacade :=
  CrossBlockFinalIntegratedW11.ArbitraryNTargetFacade

abbrev PolynomialRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.PolynomialRows F k hk

abbrev PolynomialRowFamilies (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.PolynomialRowFamilies F

abbrev GeneratedPointTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.GeneratedPointTable F k hk

abbrev PackedInequalities
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.PackedInequalities F k hk

abbrev PositionPolynomialCertificate
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.PositionPolynomialCertificate F k hk

abbrev ValueRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.ValueRows F k hk

abbrev ValueRowFamilies (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.ValueRowFamilies F

abbrev NonConnectorValueMatrix
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.NonConnectorValueMatrix F k hk

abbrev NonConnectorValueMatrixFamily (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.NonConnectorValueMatrixFamily F

abbrev NonConnectorLowerTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.NonConnectorLowerTable F k hk

abbrev NonConnectorLowerTableFamily (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.NonConnectorLowerTableFamily F

abbrev PositionValueCertificate
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.PositionValueCertificate F k hk

abbrev SqDistanceTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.SqDistanceTable F k hk

abbrev CrossBlockInequalityLedger (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.CrossBlockClosureLedger F

abbrev RoleHingeCrossBlockInequalityPackage
    (F : RoleHingeCrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.RoleHingeCrossBlockInequalityPackage F

/-! ## Shared route shape -/

/-- Exact, fixed, eventual, arbitrary, and facade projections from one
explicit input package. -/
structure ConditionalProjectionRoute (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget
  targetFacade : alpha -> ArbitraryNTargetFacade

namespace ConditionalProjectionRoute

def ofCrossBlockFinal
    {alpha : Sort u}
    (R : CrossBlockFinalIntegratedW11.ConditionalPachTothRoute alpha) :
    ConditionalProjectionRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

def ofCrossBlockFamily
    {F : CrossBlockFamily} {alpha : Sort u}
  (R : CrossBlockFinalIntegratedW11.FamilyTargetRoute F alpha) :
    ConditionalProjectionRoute alpha :=
  ofCrossBlockFinal
    (CrossBlockFinalIntegratedW11.ConditionalPachTothRoute.ofFamilyTargetRoute
      R)

def ofGeneratedFinal
    {alpha : Sort u}
    (R : GeneratedTargetFinalW11.ProjectionRoute alpha) :
    ConditionalProjectionRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := fun a n => R.arbitraryTarget a n
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := fun a =>
    { fixedTarget := fun n => R.arbitraryTarget a n
      arbitraryTarget := R.arbitraryTarget a }

end ConditionalProjectionRoute

/-! ## Explicit polynomial, value, and ledger fields -/

/-- Polynomial package shapes retained by the final cross-block layer. -/
structure ExplicitPolynomialFields where
  rows :
    forall (_F : CrossBlockFamily) (k : Nat), 0 < k -> Prop
  rowFamilies : CrossBlockFamily -> Prop
  generatedPointTables :
    forall (_F : CrossBlockFamily) (k : Nat), 0 < k -> Prop
  packedInequalities :
    forall (_F : CrossBlockFamily) (k : Nat), 0 < k -> Prop
  positionCertificates :
    forall (_F : CrossBlockFamily) (k : Nat), 0 < k -> Prop
  targetIntegrated : CrossBlockTargetIntegratedW11.PolynomialInputFields
  finalIntegrated : CrossBlockFinalIntegratedW11.ExplicitPolynomialFields

/-- Value package shapes retained by the final cross-block layer. -/
structure ExplicitValueFields where
  rows :
    forall (_F : CrossBlockFamily) (k : Nat), 0 < k -> Type
  rowFamilies : CrossBlockFamily -> Type
  valueMatrices :
    forall (_F : CrossBlockFamily) (k : Nat), 0 < k -> Type
  valueMatrixFamilies : CrossBlockFamily -> Type
  lowerTables :
    forall (_F : CrossBlockFamily) (k : Nat), 0 < k -> Prop
  lowerTableFamilies : CrossBlockFamily -> Prop
  positionCertificates :
    forall (_F : CrossBlockFamily) (k : Nat), 0 < k -> Type
  sqDistanceTables :
    forall (_F : CrossBlockFamily) (k : Nat), 0 < k -> Prop
  targetIntegrated : CrossBlockTargetIntegratedW11.ValueInputFields
  finalIntegrated : CrossBlockFinalIntegratedW11.ExplicitValueFields

/-- Ledger package shapes retained by the final cross-block layer. -/
structure ExplicitLedgerFields where
  inequalityLedgers : CrossBlockFamily -> Type
  closureLedgers : CrossBlockFamily -> Type
  roleHingeInequalityPackages :
    RoleHingeCrossBlockFamily -> Prop
  targetIntegrated : CrossBlockTargetIntegratedW11.LedgerInputFields
  finalIntegrated : CrossBlockFinalIntegratedW11.ExplicitLedgerFields

def explicitPolynomialFields : ExplicitPolynomialFields where
  rows := PolynomialRows
  rowFamilies := PolynomialRowFamilies
  generatedPointTables := GeneratedPointTable
  packedInequalities := PackedInequalities
  positionCertificates := PositionPolynomialCertificate
  targetIntegrated := CrossBlockTargetIntegratedW11.polynomialInputFields
  finalIntegrated := CrossBlockFinalIntegratedW11.explicitPolynomialFields

def explicitValueFields : ExplicitValueFields where
  rows := ValueRows
  rowFamilies := ValueRowFamilies
  valueMatrices := NonConnectorValueMatrix
  valueMatrixFamilies := NonConnectorValueMatrixFamily
  lowerTables := NonConnectorLowerTable
  lowerTableFamilies := NonConnectorLowerTableFamily
  positionCertificates := PositionValueCertificate
  sqDistanceTables := SqDistanceTable
  targetIntegrated := CrossBlockTargetIntegratedW11.valueInputFields
  finalIntegrated := CrossBlockFinalIntegratedW11.explicitValueFields

def explicitLedgerFields : ExplicitLedgerFields where
  inequalityLedgers := CrossBlockInequalityLedger
  closureLedgers := CrossBlockClosureLedger
  roleHingeInequalityPackages := RoleHingeCrossBlockInequalityPackage
  targetIntegrated := CrossBlockTargetIntegratedW11.ledgerInputFields
  finalIntegrated := CrossBlockFinalIntegratedW11.explicitLedgerFields

/-- All explicit field ledgers consumed by this final layer. -/
structure ExplicitFieldLedger where
  polynomial : ExplicitPolynomialFields
  value : ExplicitValueFields
  ledger : ExplicitLedgerFields
  crossBlockTarget :
    CrossBlockTargetIntegratedW11.ExplicitCrossBlockTargetInputs
  crossBlockFinal : CrossBlockFinalIntegratedW11.ExplicitCrossBlockFields
  generatedTargetFinal : GeneratedTargetFinalW11.ExplicitInputLedgers
  arbitraryNTargetCrossBlock : ArbitraryNTargetFinalW11.CrossBlockFields
  pachTothFinalConsistency : PachTothW11FinalConsistency.OpenInputLedgers

def explicitFieldLedger : ExplicitFieldLedger where
  polynomial := explicitPolynomialFields
  value := explicitValueFields
  ledger := explicitLedgerFields
  crossBlockTarget := CrossBlockTargetIntegratedW11.explicitCrossBlockTargetInputs
  crossBlockFinal := CrossBlockFinalIntegratedW11.explicitCrossBlockFields
  generatedTargetFinal := GeneratedTargetFinalW11.explicitInputLedgers
  arbitraryNTargetCrossBlock := ArbitraryNTargetFinalW11.matrix.crossBlock
  pachTothFinalConsistency := PachTothW11FinalConsistency.openInputLedgers

/-! ## Imported checked matrices -/

/-- Checked W11 matrices used by the final consistency layer. -/
structure ImportedMatrices where
  crossBlockTarget : CrossBlockTargetIntegratedW11.Matrix
  crossBlockFinal : CrossBlockFinalIntegratedW11.Matrix
  generatedTargetFinal : GeneratedTargetFinalW11.Matrix
  arbitraryNTargetFinal : ArbitraryNTargetFinalW11.Matrix
  pachTothFinalConsistency : PachTothW11FinalConsistency.Matrix

def importedMatrices : ImportedMatrices where
  crossBlockTarget := CrossBlockTargetIntegratedW11.matrix
  crossBlockFinal := CrossBlockFinalIntegratedW11.matrix
  generatedTargetFinal := GeneratedTargetFinalW11.matrix
  arbitraryNTargetFinal := ArbitraryNTargetFinalW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-! ## Projection ledgers -/

/-- Polynomial routes, with both target-integrated and final routes visible. -/
structure PolynomialProjectionLedger where
  targetRows :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockTargetIntegratedW11.BlockTargetRoute
        F k hk (PolynomialRows F k hk)
  finalRows :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockFinalIntegratedW11.BlockTargetRoute
        F k hk (PolynomialRows F k hk)
  generatedPointTables :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockFinalIntegratedW11.BlockTargetRoute
        F k hk (GeneratedPointTable F k hk)
  packedInequalities :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockFinalIntegratedW11.BlockTargetRoute
        F k hk (PackedInequalities F k hk)
  positionCertificates :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockFinalIntegratedW11.BlockTargetRoute
        F k hk (PositionPolynomialCertificate F k hk)
  rowFamilies :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (PolynomialRowFamilies F)
  rowFamiliesViaGeneratedFinal :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (PolynomialRowFamilies F)

def polynomialProjectionLedger : PolynomialProjectionLedger where
  targetRows := CrossBlockTargetIntegratedW11.matrix.polynomialRows.rows
  finalRows := CrossBlockFinalIntegratedW11.matrix.polynomial.rows
  generatedPointTables :=
    CrossBlockFinalIntegratedW11.matrix.polynomial.generatedPointTables
  packedInequalities :=
    CrossBlockFinalIntegratedW11.matrix.polynomial.packedInequalities
  positionCertificates :=
    CrossBlockFinalIntegratedW11.matrix.polynomial.positionCertificates
  rowFamilies := fun F =>
    ConditionalProjectionRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.polynomial.rowFamilies F)
  rowFamiliesViaGeneratedFinal := fun F =>
    ConditionalProjectionRoute.ofGeneratedFinal
      (GeneratedTargetFinalW11.matrix.crossBlock.polynomialRowFamilies F)

/-- Value routes, with both target-integrated and final routes visible. -/
structure ValueProjectionLedger where
  targetRows :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockTargetIntegratedW11.BlockTargetRoute
        F k hk (ValueRows F k hk)
  finalRows :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockFinalIntegratedW11.BlockTargetRoute
        F k hk (ValueRows F k hk)
  valueMatrices :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockFinalIntegratedW11.BlockTargetRoute
        F k hk (NonConnectorValueMatrix F k hk)
  lowerTables :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockFinalIntegratedW11.BlockTargetRoute
        F k hk (NonConnectorLowerTable F k hk)
  positionCertificates :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockFinalIntegratedW11.BlockTargetRoute
        F k hk (PositionValueCertificate F k hk)
  sqDistanceTables :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      CrossBlockFinalIntegratedW11.BlockTargetRoute
        F k hk (SqDistanceTable F k hk)
  rowFamilies :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (ValueRowFamilies F)
  rowFamiliesViaGeneratedFinal :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (ValueRowFamilies F)
  valueMatrixFamilies :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (NonConnectorValueMatrixFamily F)
  valueMatrixFamiliesViaGeneratedFinal :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (NonConnectorValueMatrixFamily F)
  lowerTableFamilies :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (NonConnectorLowerTableFamily F)
  lowerTableFamiliesViaGeneratedFinal :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (NonConnectorLowerTableFamily F)

def valueProjectionLedger : ValueProjectionLedger where
  targetRows := CrossBlockTargetIntegratedW11.matrix.valueRows.rows
  finalRows := CrossBlockFinalIntegratedW11.matrix.value.rows
  valueMatrices := CrossBlockFinalIntegratedW11.matrix.value.valueMatrices
  lowerTables := CrossBlockFinalIntegratedW11.matrix.value.lowerTables
  positionCertificates :=
    CrossBlockFinalIntegratedW11.matrix.value.positionCertificates
  sqDistanceTables := CrossBlockFinalIntegratedW11.matrix.value.sqDistanceTables
  rowFamilies := fun F =>
    ConditionalProjectionRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.value.rowFamilies F)
  rowFamiliesViaGeneratedFinal := fun F =>
    ConditionalProjectionRoute.ofGeneratedFinal
      (GeneratedTargetFinalW11.matrix.crossBlock.valueRowFamilies F)
  valueMatrixFamilies := fun F =>
    ConditionalProjectionRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.value.valueMatrixFamilies F)
  valueMatrixFamiliesViaGeneratedFinal := fun F =>
    ConditionalProjectionRoute.ofGeneratedFinal
      (GeneratedTargetFinalW11.matrix.crossBlock.valueMatrixFamilies F)
  lowerTableFamilies := fun F =>
    ConditionalProjectionRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.value.lowerTableFamilies F)
  lowerTableFamiliesViaGeneratedFinal := fun F =>
    ConditionalProjectionRoute.ofGeneratedFinal
      (GeneratedTargetFinalW11.matrix.crossBlock.lowerTableFamilies F)

/-- Ledger routes from the target, final, generated-final, and broad final
consistency layers. -/
structure LedgerProjectionLedger where
  targetInequalityLedgers :
    forall F : CrossBlockFamily,
      CrossBlockTargetIntegratedW11.FamilyTargetRoute
        F (CrossBlockInequalityLedger F)
  targetClosureLedgers :
    forall F : CrossBlockFamily,
      CrossBlockTargetIntegratedW11.FamilyTargetRoute
        F (CrossBlockClosureLedger F)
  inequalityLedgers :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (CrossBlockInequalityLedger F)
  inequalityLedgersViaGeneratedFinal :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (CrossBlockInequalityLedger F)
  inequalityLedgersViaGeneratedTarget :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (CrossBlockInequalityLedger F)
  closureLedgers :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (CrossBlockClosureLedger F)
  closureLedgersViaGeneratedFinal :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (CrossBlockClosureLedger F)
  closureLedgersViaPachTothIntegrated :
    forall F : CrossBlockFamily,
      ConditionalProjectionRoute (CrossBlockClosureLedger F)
  roleHingeInequalityPackages :
    forall F : RoleHingeCrossBlockFamily,
      ConditionalProjectionRoute (RoleHingeCrossBlockInequalityPackage F)
  inequalityViaArbitraryNTargetFinal :
    forall F : CrossBlockFamily,
      CrossBlockInequalityLedger F -> ArbitraryTarget
  closureViaArbitraryNTargetFinal :
    forall F : CrossBlockFamily,
      CrossBlockClosureLedger F -> ArbitraryTarget
  closureViaPachTothFinalConsistency :
    forall F : CrossBlockFamily,
      CrossBlockClosureLedger F -> ArbitraryTarget

def ledgerProjectionLedger : LedgerProjectionLedger where
  targetInequalityLedgers :=
    CrossBlockTargetIntegratedW11.matrix.ledgerRows.inequalityLedgers
  targetClosureLedgers :=
    CrossBlockTargetIntegratedW11.matrix.ledgerRows.closureLedgers
  inequalityLedgers := fun F =>
    ConditionalProjectionRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.ledger.inequalityLedgers F)
  inequalityLedgersViaGeneratedFinal := fun F =>
    ConditionalProjectionRoute.ofGeneratedFinal
      (GeneratedTargetFinalW11.matrix.crossBlock.inequalityLedgers F)
  inequalityLedgersViaGeneratedTarget := fun F =>
    ConditionalProjectionRoute.ofCrossBlockFinal
      (CrossBlockFinalIntegratedW11.matrix.ledger
        |>.generatedTargetInequalityLedgers F)
  closureLedgers := fun F =>
    ConditionalProjectionRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.ledger.closureLedgers F)
  closureLedgersViaGeneratedFinal := fun F =>
    ConditionalProjectionRoute.ofGeneratedFinal
      (GeneratedTargetFinalW11.matrix.crossBlock.closureLedgers F)
  closureLedgersViaPachTothIntegrated := fun F =>
    ConditionalProjectionRoute.ofCrossBlockFinal
      (CrossBlockFinalIntegratedW11.matrix.ledger
        |>.pachTothIntegratedClosureLedgers F)
  roleHingeInequalityPackages := fun F =>
    ConditionalProjectionRoute.ofCrossBlockFinal
      (CrossBlockFinalIntegratedW11.matrix.ledger
        |>.roleHingeInequalityPackages F)
  inequalityViaArbitraryNTargetFinal := fun _F L =>
    ArbitraryNTargetFinalW11.arbitraryTarget_of_crossBlockInequalityLedger L
  closureViaArbitraryNTargetFinal := fun _F C =>
    ArbitraryNTargetFinalW11.arbitraryTarget_of_crossBlockClosureLedger C
  closureViaPachTothFinalConsistency := fun _F C =>
    PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
      C

/-! ## Final matrix -/

/-- Final W11 cross-block target consistency matrix. -/
structure Matrix where
  fields : ExplicitFieldLedger
  imports : ImportedMatrices
  polynomial : PolynomialProjectionLedger
  value : ValueProjectionLedger
  ledger : LedgerProjectionLedger

def matrix : Matrix where
  fields := explicitFieldLedger
  imports := importedMatrices
  polynomial := polynomialProjectionLedger
  value := valueProjectionLedger
  ledger := ledgerProjectionLedger

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public conditional polynomial projections -/

theorem targetAt_of_polynomialRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : PolynomialRows F k hk) :
    FixedTarget (16 * k) :=
  (matrix.polynomial.finalRows F k hk).exactBlockTarget R

theorem targetAt_of_generatedPointTables
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : GeneratedPointTable F k hk) :
    FixedTarget (16 * k) :=
  (matrix.polynomial.generatedPointTables F k hk).exactBlockTarget R

theorem targetAt_of_packedInequalities
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : PackedInequalities F k hk) :
    FixedTarget (16 * k) :=
  (matrix.polynomial.packedInequalities F k hk).exactBlockTarget R

theorem targetAt_of_positionPolynomialCertificates
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : PositionPolynomialCertificate F k hk) :
    FixedTarget (16 * k) :=
  (matrix.polynomial.positionCertificates F k hk).exactBlockTarget R

theorem exactTarget_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ExactTarget :=
  (matrix.polynomial.rowFamilies F).exactTarget R

theorem fixedTarget_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) (n : Nat) :
    FixedTarget n :=
  (matrix.polynomial.rowFamilies F).fixedTarget R n

theorem eventualTarget_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    EventualTarget :=
  (matrix.polynomial.rowFamilies F).eventualTarget R

theorem arbitraryTarget_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ArbitraryTarget :=
  (matrix.polynomial.rowFamilies F).arbitraryTarget R

theorem targetFacade_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ArbitraryNTargetFacade :=
  (matrix.polynomial.rowFamilies F).targetFacade R

theorem arbitraryTarget_viaGeneratedFinal_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ArbitraryTarget :=
  (matrix.polynomial.rowFamiliesViaGeneratedFinal F).arbitraryTarget R

/-! ## Public conditional value projections -/

theorem targetAt_of_valueRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : ValueRows F k hk) :
    FixedTarget (16 * k) :=
  (matrix.value.finalRows F k hk).exactBlockTarget R

theorem targetAt_of_valueMatrices
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : NonConnectorValueMatrix F k hk) :
    FixedTarget (16 * k) :=
  (matrix.value.valueMatrices F k hk).exactBlockTarget R

theorem targetAt_of_lowerTables
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : NonConnectorLowerTable F k hk) :
    FixedTarget (16 * k) :=
  (matrix.value.lowerTables F k hk).exactBlockTarget R

theorem targetAt_of_positionValueCertificates
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : PositionValueCertificate F k hk) :
    FixedTarget (16 * k) :=
  (matrix.value.positionCertificates F k hk).exactBlockTarget R

theorem targetAt_of_sqDistanceTables
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : SqDistanceTable F k hk) :
    FixedTarget (16 * k) :=
  (matrix.value.sqDistanceTables F k hk).exactBlockTarget R

theorem exactTarget_of_valueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    ExactTarget :=
  (matrix.value.rowFamilies F).exactTarget R

theorem eventualTarget_of_valueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    EventualTarget :=
  (matrix.value.rowFamilies F).eventualTarget R

theorem arbitraryTarget_of_valueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    ArbitraryTarget :=
  (matrix.value.rowFamilies F).arbitraryTarget R

theorem targetFacade_of_valueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    ArbitraryNTargetFacade :=
  (matrix.value.rowFamilies F).targetFacade R

theorem exactTarget_of_valueMatrixFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorValueMatrixFamily F) :
    ExactTarget :=
  (matrix.value.valueMatrixFamilies F).exactTarget R

theorem eventualTarget_of_valueMatrixFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorValueMatrixFamily F) :
    EventualTarget :=
  (matrix.value.valueMatrixFamilies F).eventualTarget R

theorem arbitraryTarget_of_valueMatrixFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorValueMatrixFamily F) :
    ArbitraryTarget :=
  (matrix.value.valueMatrixFamilies F).arbitraryTarget R

theorem exactTarget_of_lowerTableFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorLowerTableFamily F) :
    ExactTarget :=
  (matrix.value.lowerTableFamilies F).exactTarget R

theorem eventualTarget_of_lowerTableFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorLowerTableFamily F) :
    EventualTarget :=
  (matrix.value.lowerTableFamilies F).eventualTarget R

theorem arbitraryTarget_of_lowerTableFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorLowerTableFamily F) :
    ArbitraryTarget :=
  (matrix.value.lowerTableFamilies F).arbitraryTarget R

/-! ## Public conditional ledger projections -/

theorem separated_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  (matrix.ledger.targetInequalityLedgers F).separated L k hk

theorem targetAt_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (16 * k) :=
  (matrix.ledger.targetInequalityLedgers F).exactBlockTarget L k hk

theorem exactTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ExactTarget :=
  (matrix.ledger.inequalityLedgers F).exactTarget L

theorem fixedTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    FixedTarget n :=
  (matrix.ledger.inequalityLedgers F).fixedTarget L n

theorem eventualTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    EventualTarget :=
  (matrix.ledger.inequalityLedgers F).eventualTarget L

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.ledger.inequalityLedgers F).arbitraryTarget L

theorem targetFacade_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.ledger.inequalityLedgersViaGeneratedTarget F).targetFacade L

theorem arbitraryTarget_viaGeneratedFinal_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.ledger.inequalityLedgersViaGeneratedFinal F).arbitraryTarget L

theorem arbitraryTarget_viaArbitraryNFinal_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  matrix.ledger.inequalityViaArbitraryNTargetFinal F L

theorem separated_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  (matrix.ledger.targetClosureLedgers F).separated C k hk

theorem targetAt_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (16 * k) :=
  (matrix.ledger.targetClosureLedgers F).exactBlockTarget C k hk

theorem exactTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ExactTarget :=
  (matrix.ledger.closureLedgers F).exactTarget C

theorem fixedTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) (n : Nat) :
    FixedTarget n :=
  (matrix.ledger.closureLedgers F).fixedTarget C n

theorem eventualTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    EventualTarget :=
  (matrix.ledger.closureLedgers F).eventualTarget C

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.ledger.closureLedgers F).arbitraryTarget C

theorem targetFacade_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.ledger.closureLedgers F).targetFacade C

theorem arbitraryTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.ledger.closureLedgersViaPachTothIntegrated F).arbitraryTarget C

theorem arbitraryTarget_viaArbitraryNFinal_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.ledger.closureViaArbitraryNTargetFinal F C

theorem arbitraryTarget_viaPachTothFinalConsistency_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.ledger.closureViaPachTothFinalConsistency F C

theorem exactTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ExactTarget :=
  (matrix.ledger.roleHingeInequalityPackages F).exactTarget R

theorem eventualTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    EventualTarget :=
  (matrix.ledger.roleHingeInequalityPackages F).eventualTarget R

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.ledger.roleHingeInequalityPackages F).arbitraryTarget R

end

end CrossBlockTargetFinalW11
end PachToth
end ErdosProblems1066
