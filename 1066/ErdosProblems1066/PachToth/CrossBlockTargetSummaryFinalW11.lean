import ErdosProblems1066.PachToth.CrossBlockTargetFinalW11
import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.GeneratedCrossBlockFinalW11
import ErdosProblems1066.PachToth.RoleHingeTargetFinalW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false

/-!
# W11 final cross-block target summary

This leaf module records the checked cross-block target ledgers used by the
W11 final route files.  It keeps the polynomial, value, and ledger fields
visible, and exposes only projections that still require their input package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockTargetSummaryFinalW11

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
  CrossBlockTargetFinalW11.CrossBlockFamily

abbrev RoleHingeCrossBlockFamily :=
  CrossBlockTargetFinalW11.RoleHingeCrossBlockFamily

abbrev RoleHingeTargetCrossBlockFamily :=
  RoleHingeTargetFinalW11.CrossBlockRoleHingeFamily

abbrev PolynomialRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetFinalW11.PolynomialRows F k hk

abbrev PolynomialRowFamilies (F : CrossBlockFamily) :=
  CrossBlockTargetFinalW11.PolynomialRowFamilies F

abbrev GeneratedPointTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetFinalW11.GeneratedPointTable F k hk

abbrev PackedInequalities
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetFinalW11.PackedInequalities F k hk

abbrev PositionPolynomialCertificate
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetFinalW11.PositionPolynomialCertificate F k hk

abbrev ValueRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetFinalW11.ValueRows F k hk

abbrev ValueRowFamilies (F : CrossBlockFamily) :=
  CrossBlockTargetFinalW11.ValueRowFamilies F

abbrev NonConnectorValueMatrix
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetFinalW11.NonConnectorValueMatrix F k hk

abbrev NonConnectorValueMatrixFamily (F : CrossBlockFamily) :=
  CrossBlockTargetFinalW11.NonConnectorValueMatrixFamily F

abbrev NonConnectorLowerTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetFinalW11.NonConnectorLowerTable F k hk

abbrev NonConnectorLowerTableFamily (F : CrossBlockFamily) :=
  CrossBlockTargetFinalW11.NonConnectorLowerTableFamily F

abbrev PositionValueCertificate
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetFinalW11.PositionValueCertificate F k hk

abbrev SqDistanceTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetFinalW11.SqDistanceTable F k hk

abbrev CrossBlockInequalityLedger (F : CrossBlockFamily) :=
  CrossBlockTargetFinalW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger (F : CrossBlockFamily) :=
  CrossBlockTargetFinalW11.CrossBlockClosureLedger F

abbrev RoleHingeCrossBlockInequalityPackage
    (F : RoleHingeCrossBlockFamily) :=
  CrossBlockTargetFinalW11.RoleHingeCrossBlockInequalityPackage F

abbrev RoleHingeTargetInequalityPackage
    (F : RoleHingeTargetCrossBlockFamily) :=
  RoleHingeTargetFinalW11.RoleHingeCrossBlockInequalityPackage F

/-! ## Checked ledgers -/

/-- Checked W11 ledgers used by this summary. -/
structure CheckedLedgers where
  crossBlockTarget : CrossBlockTargetFinalW11.Matrix
  crossBlockFinal : CrossBlockFinalIntegratedW11.Matrix
  generatedCrossBlock : GeneratedCrossBlockFinalW11.Matrix
  roleHingeTarget : RoleHingeTargetFinalW11.Matrix
  pachTothFinalAggregate : PachTothW11FinalAggregate.Matrix

/-- Imported checked W11 cross-block ledgers. -/
def checkedLedgers : CheckedLedgers where
  crossBlockTarget := CrossBlockTargetFinalW11.matrix
  crossBlockFinal := CrossBlockFinalIntegratedW11.matrix
  generatedCrossBlock := GeneratedCrossBlockFinalW11.matrix
  roleHingeTarget := RoleHingeTargetFinalW11.matrix
  pachTothFinalAggregate := PachTothW11FinalAggregate.matrix

/-! ## Explicit field ledgers -/

/-- Polynomial fields retained by the summary. -/
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
  targetFinal : CrossBlockTargetFinalW11.ExplicitPolynomialFields
  finalIntegrated : CrossBlockFinalIntegratedW11.ExplicitPolynomialFields
  aggregateCrossBlock : PachTothW11FinalAggregate.ExplicitCrossBlockData

/-- Value fields retained by the summary. -/
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
  targetFinal : CrossBlockTargetFinalW11.ExplicitValueFields
  finalIntegrated : CrossBlockFinalIntegratedW11.ExplicitValueFields
  aggregateCrossBlock : PachTothW11FinalAggregate.ExplicitCrossBlockData

/-- Ledger fields retained by the summary. -/
structure ExplicitLedgerFields where
  inequalityLedgers : CrossBlockFamily -> Type
  closureLedgers : CrossBlockFamily -> Type
  roleHingeInequalityPackages :
    RoleHingeCrossBlockFamily -> Prop
  roleHingeTargetPackages :
    RoleHingeTargetCrossBlockFamily -> Prop
  targetFinal : CrossBlockTargetFinalW11.ExplicitLedgerFields
  finalIntegrated : CrossBlockFinalIntegratedW11.ExplicitLedgerFields
  generatedCrossBlock : GeneratedCrossBlockFinalW11.ExplicitFinalLedgers
  roleHingeTarget : RoleHingeTargetFinalW11.RoleHingeTargetFieldLedger
  aggregateCrossBlock : PachTothW11FinalAggregate.ExplicitCrossBlockData

/-- Explicit polynomial fields. -/
def explicitPolynomialFields : ExplicitPolynomialFields where
  rows := PolynomialRows
  rowFamilies := PolynomialRowFamilies
  generatedPointTables := GeneratedPointTable
  packedInequalities := PackedInequalities
  positionCertificates := PositionPolynomialCertificate
  targetFinal := CrossBlockTargetFinalW11.explicitPolynomialFields
  finalIntegrated := CrossBlockFinalIntegratedW11.explicitPolynomialFields
  aggregateCrossBlock := PachTothW11FinalAggregate.explicitCrossBlockData

/-- Explicit value fields. -/
def explicitValueFields : ExplicitValueFields where
  rows := ValueRows
  rowFamilies := ValueRowFamilies
  valueMatrices := NonConnectorValueMatrix
  valueMatrixFamilies := NonConnectorValueMatrixFamily
  lowerTables := NonConnectorLowerTable
  lowerTableFamilies := NonConnectorLowerTableFamily
  positionCertificates := PositionValueCertificate
  sqDistanceTables := SqDistanceTable
  targetFinal := CrossBlockTargetFinalW11.explicitValueFields
  finalIntegrated := CrossBlockFinalIntegratedW11.explicitValueFields
  aggregateCrossBlock := PachTothW11FinalAggregate.explicitCrossBlockData

/-- Explicit ledger fields. -/
def explicitLedgerFields : ExplicitLedgerFields where
  inequalityLedgers := CrossBlockInequalityLedger
  closureLedgers := CrossBlockClosureLedger
  roleHingeInequalityPackages := RoleHingeCrossBlockInequalityPackage
  roleHingeTargetPackages := RoleHingeTargetInequalityPackage
  targetFinal := CrossBlockTargetFinalW11.explicitLedgerFields
  finalIntegrated := CrossBlockFinalIntegratedW11.explicitLedgerFields
  generatedCrossBlock := GeneratedCrossBlockFinalW11.explicitFinalLedgers
  roleHingeTarget := RoleHingeTargetFinalW11.roleHingeTargetFieldLedger
  aggregateCrossBlock := PachTothW11FinalAggregate.explicitCrossBlockData

/-- Explicit field summary. -/
structure ExplicitFields where
  polynomial : ExplicitPolynomialFields
  value : ExplicitValueFields
  ledger : ExplicitLedgerFields
  targetFinal : CrossBlockTargetFinalW11.ExplicitFieldLedger
  finalCrossBlock : CrossBlockFinalIntegratedW11.ExplicitCrossBlockFields
  generatedCrossBlock : GeneratedCrossBlockFinalW11.ExplicitFinalLedgers
  roleHingeTarget : RoleHingeTargetFinalW11.RoleHingeTargetFieldLedger
  aggregateOpenData : PachTothW11FinalAggregate.ExplicitOpenData

/-- Combined explicit field ledger. -/
def explicitFields : ExplicitFields where
  polynomial := explicitPolynomialFields
  value := explicitValueFields
  ledger := explicitLedgerFields
  targetFinal := CrossBlockTargetFinalW11.explicitFieldLedger
  finalCrossBlock := CrossBlockFinalIntegratedW11.explicitCrossBlockFields
  generatedCrossBlock := GeneratedCrossBlockFinalW11.explicitFinalLedgers
  roleHingeTarget := RoleHingeTargetFinalW11.roleHingeTargetFieldLedger
  aggregateOpenData := PachTothW11FinalAggregate.explicitOpenData

/-! ## Conditional route shapes -/

/-- Exact, eventual, and arbitrary projections from an explicit package. -/
structure ConditionalProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace ConditionalProjection

def ofCrossBlockTarget
    {alpha : Sort u}
    (R : CrossBlockTargetFinalW11.ConditionalProjectionRoute alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofCrossBlockFinal
    {alpha : Sort u}
    (R : CrossBlockFinalIntegratedW11.ConditionalPachTothRoute alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofGeneratedCrossBlock
    {alpha : Sort u}
    (R : GeneratedCrossBlockFinalW11.ConditionalRoute alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofRoleHingeTarget
    {alpha : Sort u}
    (R : RoleHingeTargetFinalW11.TargetProjection alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end ConditionalProjection

/-- Conditional projections that also include every fixed `n`. -/
structure FixedConditionalProjection (alpha : Sort u) :
    Sort (max 1 u) where
  toConditionalProjection : ConditionalProjection alpha
  fixedTarget : alpha -> forall n : Nat, FixedTarget n

namespace FixedConditionalProjection

def ofCrossBlockTarget
    {alpha : Sort u}
    (R : CrossBlockTargetFinalW11.ConditionalProjectionRoute alpha) :
    FixedConditionalProjection alpha where
  toConditionalProjection :=
    ConditionalProjection.ofCrossBlockTarget R
  fixedTarget := R.fixedTarget

def ofCrossBlockFinal
    {alpha : Sort u}
    (R : CrossBlockFinalIntegratedW11.ConditionalPachTothRoute alpha) :
    FixedConditionalProjection alpha where
  toConditionalProjection :=
    ConditionalProjection.ofCrossBlockFinal R
  fixedTarget := R.fixedTarget

def ofGeneratedCrossBlock
    {alpha : Sort u}
    (R : GeneratedCrossBlockFinalW11.FixedConditionalRoute alpha) :
    FixedConditionalProjection alpha where
  toConditionalProjection :=
    { exactTarget := R.exactTarget
      eventualTarget := R.eventualTarget
      arbitraryTarget := R.arbitraryTarget }
  fixedTarget := R.fixedTarget

end FixedConditionalProjection

/-! ## Projection summaries -/

/-- Conditional polynomial projections retained by the summary. -/
structure PolynomialProjectionSummary where
  rows :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      PolynomialRows F k hk -> FixedTarget (16 * k)
  generatedPointTables :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      GeneratedPointTable F k hk -> FixedTarget (16 * k)
  packedInequalities :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      PackedInequalities F k hk -> FixedTarget (16 * k)
  positionCertificates :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      PositionPolynomialCertificate F k hk -> FixedTarget (16 * k)
  rowFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (PolynomialRowFamilies F)
  rowFamiliesViaGenerated :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (PolynomialRowFamilies F)

/-- Checked polynomial projections. -/
def polynomialProjectionSummary : PolynomialProjectionSummary where
  rows := fun _F _k _hk R =>
    CrossBlockTargetFinalW11.targetAt_of_polynomialRows R
  generatedPointTables := fun _F _k _hk R =>
    CrossBlockTargetFinalW11.targetAt_of_generatedPointTables R
  packedInequalities := fun _F _k _hk R =>
    CrossBlockTargetFinalW11.targetAt_of_packedInequalities R
  positionCertificates := fun _F _k _hk R =>
    CrossBlockTargetFinalW11.targetAt_of_positionPolynomialCertificates R
  rowFamilies := fun F =>
    FixedConditionalProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.polynomial.rowFamilies F)
  rowFamiliesViaGenerated := fun F =>
    FixedConditionalProjection.ofGeneratedCrossBlock
      (GeneratedCrossBlockFinalW11.matrix.crossBlock.polynomialRowFamilies F)

/-- Conditional value projections retained by the summary. -/
structure ValueProjectionSummary where
  rows :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      ValueRows F k hk -> FixedTarget (16 * k)
  valueMatrices :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      NonConnectorValueMatrix F k hk -> FixedTarget (16 * k)
  lowerTables :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      NonConnectorLowerTable F k hk -> FixedTarget (16 * k)
  positionCertificates :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      PositionValueCertificate F k hk -> FixedTarget (16 * k)
  sqDistanceTables :
    forall (F : CrossBlockFamily) (k : Nat) (hk : 0 < k),
      SqDistanceTable F k hk -> FixedTarget (16 * k)
  rowFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (ValueRowFamilies F)
  valueMatrixFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (NonConnectorValueMatrixFamily F)
  lowerTableFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (NonConnectorLowerTableFamily F)

/-- Checked value projections. -/
def valueProjectionSummary : ValueProjectionSummary where
  rows := fun _F _k _hk R =>
    CrossBlockTargetFinalW11.targetAt_of_valueRows R
  valueMatrices := fun _F _k _hk R =>
    CrossBlockTargetFinalW11.targetAt_of_valueMatrices R
  lowerTables := fun _F _k _hk R =>
    CrossBlockTargetFinalW11.targetAt_of_lowerTables R
  positionCertificates := fun _F _k _hk R =>
    CrossBlockTargetFinalW11.targetAt_of_positionValueCertificates R
  sqDistanceTables := fun _F _k _hk R =>
    CrossBlockTargetFinalW11.targetAt_of_sqDistanceTables R
  rowFamilies := fun F =>
    FixedConditionalProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.value.rowFamilies F)
  valueMatrixFamilies := fun F =>
    FixedConditionalProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.value.valueMatrixFamilies F)
  lowerTableFamilies := fun F =>
    FixedConditionalProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.value.lowerTableFamilies F)

/-- Conditional ledger projections retained by the summary. -/
structure LedgerProjectionSummary where
  inequalityLedgers :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (CrossBlockInequalityLedger F)
  inequalityLedgersViaGenerated :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (CrossBlockInequalityLedger F)
  closureLedgers :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (CrossBlockClosureLedger F)
  closureLedgersViaGenerated :
    forall F : CrossBlockFamily,
      FixedConditionalProjection (CrossBlockClosureLedger F)
  closureLedgersViaAggregate :
    forall F : CrossBlockFamily,
      CrossBlockClosureLedger F -> ArbitraryTarget
  roleHingePackages :
    forall F : RoleHingeCrossBlockFamily,
      FixedConditionalProjection (RoleHingeCrossBlockInequalityPackage F)
  roleHingeTargetPackages :
    forall F : RoleHingeTargetCrossBlockFamily,
      ConditionalProjection (RoleHingeTargetInequalityPackage F)

/-- Checked ledger projections. -/
def ledgerProjectionSummary : LedgerProjectionSummary where
  inequalityLedgers := fun F =>
    FixedConditionalProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.ledger.inequalityLedgers F)
  inequalityLedgersViaGenerated := fun F =>
    FixedConditionalProjection.ofGeneratedCrossBlock
      (GeneratedCrossBlockFinalW11.matrix.crossBlock.inequalityLedgers F)
  closureLedgers := fun F =>
    FixedConditionalProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.ledger.closureLedgers F)
  closureLedgersViaGenerated := fun F =>
    FixedConditionalProjection.ofGeneratedCrossBlock
      (GeneratedCrossBlockFinalW11.matrix.crossBlock.closureLedgers F)
  closureLedgersViaAggregate := fun _F C =>
    PachTothW11FinalAggregate.arbitraryTarget_of_crossBlockClosureLedger C
  roleHingePackages := fun F =>
    FixedConditionalProjection.ofCrossBlockTarget
      (CrossBlockTargetFinalW11.matrix.ledger.roleHingeInequalityPackages F)
  roleHingeTargetPackages := fun F =>
    ConditionalProjection.ofRoleHingeTarget
      (RoleHingeTargetFinalW11.matrix.crossBlockLowerBound
        |>.roleHingeInequalityPackage F)

/-! ## Final summary matrix -/

/-- Final checked cross-block target summary. -/
structure Matrix where
  checked : CheckedLedgers
  fields : ExplicitFields
  polynomial : PolynomialProjectionSummary
  value : ValueProjectionSummary
  ledger : LedgerProjectionSummary

/-- The final checked cross-block target summary. -/
def matrix : Matrix where
  checked := checkedLedgers
  fields := explicitFields
  polynomial := polynomialProjectionSummary
  value := valueProjectionSummary
  ledger := ledgerProjectionSummary

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public polynomial projections -/

theorem targetAt_of_polynomialRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : PolynomialRows F k hk) :
    FixedTarget (16 * k) :=
  matrix.polynomial.rows F k hk R

theorem exactTarget_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ExactTarget :=
  (matrix.polynomial.rowFamilies F).toConditionalProjection.exactTarget R

theorem arbitraryTarget_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ArbitraryTarget :=
  (matrix.polynomial.rowFamilies F).toConditionalProjection.arbitraryTarget R

theorem arbitraryTarget_viaGenerated_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ArbitraryTarget :=
  (matrix.polynomial.rowFamiliesViaGenerated F)
    |>.toConditionalProjection
    |>.arbitraryTarget R

/-! ## Public value projections -/

theorem targetAt_of_valueRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : ValueRows F k hk) :
    FixedTarget (16 * k) :=
  matrix.value.rows F k hk R

theorem arbitraryTarget_of_valueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    ArbitraryTarget :=
  (matrix.value.rowFamilies F).toConditionalProjection.arbitraryTarget R

theorem arbitraryTarget_of_valueMatrixFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorValueMatrixFamily F) :
    ArbitraryTarget :=
  (matrix.value.valueMatrixFamilies F).toConditionalProjection.arbitraryTarget R

theorem arbitraryTarget_of_lowerTableFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorLowerTableFamily F) :
    ArbitraryTarget :=
  (matrix.value.lowerTableFamilies F).toConditionalProjection.arbitraryTarget R

/-! ## Public ledger projections -/

theorem exactTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ExactTarget :=
  (matrix.ledger.inequalityLedgers F).toConditionalProjection.exactTarget L

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.ledger.inequalityLedgers F).toConditionalProjection.arbitraryTarget L

theorem arbitraryTarget_viaGenerated_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.ledger.inequalityLedgersViaGenerated F)
    |>.toConditionalProjection
    |>.arbitraryTarget L

theorem exactTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ExactTarget :=
  (matrix.ledger.closureLedgers F).toConditionalProjection.exactTarget C

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.ledger.closureLedgers F).toConditionalProjection.arbitraryTarget C

theorem arbitraryTarget_viaGenerated_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.ledger.closureLedgersViaGenerated F)
    |>.toConditionalProjection
    |>.arbitraryTarget C

theorem arbitraryTarget_viaAggregate_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.ledger.closureLedgersViaAggregate F C

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.ledger.roleHingePackages F)
    |>.toConditionalProjection
    |>.arbitraryTarget R

theorem arbitraryTarget_of_roleHingeTargetInequalityPackage
    {F : RoleHingeTargetCrossBlockFamily}
    (R : RoleHingeTargetInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.ledger.roleHingeTargetPackages F).arbitraryTarget R

end

end CrossBlockTargetSummaryFinalW11
end PachToth
end ErdosProblems1066
