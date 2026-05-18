import ErdosProblems1066.PachToth.FiniteSearchCertificate
import ErdosProblems1066.PachToth.FiniteCertificateSearchSurface

set_option autoImplicit false

/-!
# W12 finite-certificate obligations

This file is a compact all-positive facade for the Pach-Toth finite
certificate route.  It keeps the finite search data honest: orientation
words, indexed period equations, and non-connector square-value tables are
explicit inputs, while the target theorems below are only projections through
the checked period, separation, and exact-to-arbitrary bridges.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteCertificateObligationsW12

noncomputable section

abbrev RoleHingeTransitions :=
  FiniteSearchCertificate.RoleHingeTransitions

abbrev RoleHingedPeriodSearchFamily :=
  FiniteSearchCertificate.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  FiniteSearchCertificate.LocalVertexIndex

abbrev AllPositivePeriodSearchData :=
  FiniteSearchCertificate.AllPositivePeriodSearchData

abbrev NonConnectorSqValueCertificate :=
  FiniteSearchCertificate.NonConnectorSqValueCertificate

abbrev AllPositiveNonConnectorSqValueCertificate :=
  FiniteSearchCertificate.AllPositiveNonConnectorSqValueCertificate

abbrev UpperTriangleNonConnectorSqValueTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily

abbrev VectorTableFamily :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificateFamily

abbrev ListTableFamily :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificateFamily

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev ExactBlockTarget (k : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt (16 * k)

/-! ## Period equations -/

/-- Raw all-positive period-equation fields.

The `equation` field is indexed by `Fin 16`, matching the concrete local
vertex enumeration used by the period-search interface. -/
structure PeriodEquationFields where
  transitions : RoleHingeTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k) (i : Fin 16),
      PeriodSearchInterface.AlgebraicVertexPeriodEquation
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hk))
        (BlockPartition.localVertexEquivFin16.symm i)

namespace PeriodEquationFields

/-- The generated-chain orientation carried by the stored finite word. -/
def orientation
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (P.word k hk).toFin

@[simp]
theorem orientation_apply
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    P.orientation k hk i = P.word k hk i :=
  rfl

/-- The period-search word projected from one stored orientation word. -/
def finiteWord
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodCertificateExamples.finiteOrientationWordOfWord hk (P.word k hk)

@[simp]
theorem finiteWord_length
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    (P.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (P.finiteWord k hk).letter i = P.orientation k hk i :=
  rfl

/-- Repackage the raw `Fin 16` equations as the indexed period certificate. -/
def indexedCertificate
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      P.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (P.finiteWord k hk) where
  equation := P.equation k hk

/-- The all-positive period-search package exposed by the raw fields. -/
def toPeriodSearchData
    (P : PeriodEquationFields) :
    AllPositivePeriodSearchData where
  transitions := P.transitions
  word := P.word
  period := P.indexedCertificate

@[simp]
theorem toPeriodSearchData_transitions
    (P : PeriodEquationFields) :
    P.toPeriodSearchData.transitions = P.transitions :=
  rfl

@[simp]
theorem toPeriodSearchData_word
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toPeriodSearchData.word k hk = P.word k hk :=
  rfl

@[simp]
theorem toPeriodSearchData_orientation
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toPeriodSearchData.orientation k hk = P.orientation k hk :=
  rfl

/-- The role-hinged period-search family consumed by square-table hooks. -/
def toRoleHingedPeriodSearchFamily
    (P : PeriodEquationFields) :
    RoleHingedPeriodSearchFamily :=
  P.toPeriodSearchData.toRoleHingedPeriodSearchFamily

@[simp]
theorem toRoleHingedPeriodSearchFamily_transitions
    (P : PeriodEquationFields) :
    P.toRoleHingedPeriodSearchFamily.transitions = P.transitions :=
  rfl

@[simp]
theorem toRoleHingedPeriodSearchFamily_orientation
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toRoleHingedPeriodSearchFamily.orientation k hk =
      P.orientation k hk :=
  rfl

/-- Algebraic closure obtained from the stored indexed equations. -/
def closure
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  (P.indexedCertificate k hk).toGeneratedClosureEquation

/-- Generated final-block period equation obtained from the same indexed
equations. -/
def periodEquation
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  (P.indexedCertificate k hk).toGeneratedPeriodEquation

/-- Generated-period hook consumed by the generated-chain target route. -/
def generatedPeriod
    (P : PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  (P.indexedCertificate k hk).toGeneratedPeriod

end PeriodEquationFields

/-! ## Compact non-connector square-value obligations -/

/-- Raw all-positive non-connector square-value fields over raw period
equation fields.  Only upper-triangle non-connector entries are required:
successor connector pairs are discharged by the role-hinge connector facts. -/
structure AllPositiveNonConnectorFields where
  period : PeriodEquationFields
  value :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (CrossBlockSqTableSearch.IndexedCyclicConnectorPair
            hk i u j v) ->
            value k hk i u j v =
              CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                period.toRoleHingedPeriodSearchFamily hk i u j v
  value_ge_one_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (CrossBlockSqTableSearch.IndexedCyclicConnectorPair
            hk i u j v) ->
            1 <= value k hk i u j v

namespace AllPositiveNonConnectorFields

def transitions
    (C : AllPositiveNonConnectorFields) :
    RoleHingeTransitions :=
  C.period.transitions

def orientation
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  C.period.orientation k hk

@[simp]
theorem orientation_apply
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    C.orientation k hk i = C.period.word k hk i :=
  rfl

/-- Repackage the raw square values as the checked non-connector certificate. -/
def toSqValueCertificate
    (C : AllPositiveNonConnectorFields) :
    NonConnectorSqValueCertificate C.period.toPeriodSearchData where
  value := C.value
  value_eq_polynomial_lt := by
    intro k hk i u j v hlt hnot_connector
    exact C.value_eq_polynomial_lt k hk i u j v hlt hnot_connector
  value_ge_one_lt := by
    intro k hk i u j v hlt hnot_connector
    exact C.value_ge_one_lt k hk i u j v hlt hnot_connector

/-- The compact all-positive certificate used by `FiniteSearchCertificate`. -/
def toCertificate
    (C : AllPositiveNonConnectorFields) :
    AllPositiveNonConnectorSqValueCertificate where
  periodSearch := C.period.toPeriodSearchData
  sqValue := C.toSqValueCertificate

/-- Native upper-triangle non-connector square-value table family. -/
def toSqValueTableFamily
    (C : AllPositiveNonConnectorFields) :
    UpperTriangleNonConnectorSqValueTableFamily
      C.period.toRoleHingedPeriodSearchFamily :=
  C.toSqValueCertificate.toSqValueTableFamily

/-- Non-connector square-distance table family used by the separation hook. -/
def toNonConnectorSqDistanceTableFamily
    (C : AllPositiveNonConnectorFields) :
    FiniteSearchCertificate.IndexedNonConnectorCrossBlockSqDistanceTableFamily
      C.period.toRoleHingedPeriodSearchFamily :=
  C.toSqValueCertificate.toNonConnectorSqDistanceTableFamily

/-- Generated separation obtained from the non-connector table family and
the connector-unit facts. -/
def separated
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  C.toSqValueCertificate.separated k hk

/-- Reduced metric hypotheses: separation plus the checked exact-base
same-block and transition-preservation facts. -/
def reducedMetricHypotheses
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      C.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  GeneratedMetricClosure.generatedReducedMetricHypotheses
    C.transitions hk (C.orientation k hk) (C.separated k hk)

/-- Generated-chain family exposed by the raw W12 fields. -/
def toGeneratedChainFamily
    (C : AllPositiveNonConnectorFields) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => C.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := C.orientation

/-- Period hooks for the generated-chain family. -/
def generatedPeriods
    (C : AllPositiveNonConnectorFields) :
    C.toGeneratedChainFamily.Periods :=
  fun k hk => C.period.generatedPeriod k hk

/-- Reduced metric hooks for the generated-chain family. -/
def toReducedMetricHypotheses
    (C : AllPositiveNonConnectorFields) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      C.toGeneratedChainFamily where
  metric := C.reducedMetricHypotheses

/-- Exact-block target at a chosen positive period length, using the
generated-period and reduced-metric hooks exposed above. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock_reduced
    C.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (C.orientation k hk)
    (C.period.generatedPeriod k hk)
    (C.reducedMetricHypotheses k hk)

/-- Exact target routed through generated periods and reduced metrics. -/
theorem targetUpperConstructionFiveSixteen_viaGeneratedPeriod
    (C : AllPositiveNonConnectorFields) :
    ExactTarget :=
  GeneratedSeparationInterface.targetUpperConstructionFiveSixteen_of_family_reduced
    C.toGeneratedChainFamily C.generatedPeriods C.toReducedMetricHypotheses

/-- Exact target routed through the compact all-positive certificate. -/
theorem targetUpperConstructionFiveSixteen
    (C : AllPositiveNonConnectorFields) :
    ExactTarget :=
  C.toCertificate.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target from the generated-period exact route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_viaGeneratedPeriod
    (C : AllPositiveNonConnectorFields) :
    ArbitraryTarget :=
  ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    C.targetUpperConstructionFiveSixteen_viaGeneratedPeriod

/-- Arbitrary-`n` target routed through the compact all-positive certificate. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (C : AllPositiveNonConnectorFields) :
    ArbitraryTarget :=
  C.toCertificate.targetUpperConstructionFiveSixteenArbitrary

end AllPositiveNonConnectorFields

/-! ## Native table-family and literal-table adapters -/

/-- Compact package when generated output already produces native
non-connector square-value table families. -/
structure TableFamilyPackage where
  period : PeriodEquationFields
  tableFamily :
    UpperTriangleNonConnectorSqValueTableFamily
      period.toRoleHingedPeriodSearchFamily

namespace TableFamilyPackage

/-- Flatten native non-connector tables to the raw W12 field package. -/
def toFields
    (P : TableFamilyPackage) :
    AllPositiveNonConnectorFields where
  period := P.period
  value := fun k hk => (P.tableFamily.table k hk).value
  value_eq_polynomial_lt := by
    intro k hk i u j v hlt hnot_connector
    exact
      (P.tableFamily.table k hk).value_eq_polynomial_lt
        i u j v hlt hnot_connector
  value_ge_one_lt := by
    intro k hk i u j v hlt hnot_connector
    exact
      (P.tableFamily.table k hk).value_ge_one_lt
        i u j v hlt hnot_connector

def separated
    (P : TableFamilyPackage)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      P.period.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.period.orientation k hk) :=
  P.toFields.separated k hk

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (P : TableFamilyPackage)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  P.toFields.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem targetUpperConstructionFiveSixteen
    (P : TableFamilyPackage) :
    ExactTarget :=
  P.toFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (P : TableFamilyPackage) :
    ArbitraryTarget :=
  P.toFields.targetUpperConstructionFiveSixteenArbitrary

end TableFamilyPackage

/-- Compact package for literal vector-grid generated output. -/
structure VectorPackage where
  period : PeriodEquationFields
  tables : VectorTableFamily period.toRoleHingedPeriodSearchFamily

namespace VectorPackage

def toTableFamilyPackage
    (P : VectorPackage) :
    TableFamilyPackage where
  period := P.period
  tableFamily := P.tables.toSqValueTableFamily

def toFields
    (P : VectorPackage) :
    AllPositiveNonConnectorFields :=
  P.toTableFamilyPackage.toFields

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (P : VectorPackage)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  P.toFields.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem targetUpperConstructionFiveSixteen
    (P : VectorPackage) :
    ExactTarget :=
  P.toFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (P : VectorPackage) :
    ArbitraryTarget :=
  P.toFields.targetUpperConstructionFiveSixteenArbitrary

end VectorPackage

/-- Compact package for explicit row-list generated output. -/
structure ListPackage where
  period : PeriodEquationFields
  tables : ListTableFamily period.toRoleHingedPeriodSearchFamily

namespace ListPackage

def toTableFamilyPackage
    (P : ListPackage) :
    TableFamilyPackage where
  period := P.period
  tableFamily := P.tables.toSqValueTableFamily

def toFields
    (P : ListPackage) :
    AllPositiveNonConnectorFields :=
  P.toTableFamilyPackage.toFields

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (P : ListPackage)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  P.toFields.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem targetUpperConstructionFiveSixteen
    (P : ListPackage) :
    ExactTarget :=
  P.toFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (P : ListPackage) :
    ArbitraryTarget :=
  P.toFields.targetUpperConstructionFiveSixteenArbitrary

end ListPackage

/-! ## Projection matrix -/

universe u

/-- A target-producing W12 row. -/
structure ProjectionRow (alpha : Sort u) where
  exactBlock : alpha -> forall (k : Nat), 0 < k -> ExactBlockTarget k
  exactTarget : alpha -> ExactTarget
  arbitraryTarget : alpha -> ArbitraryTarget

def rawFieldsRow : ProjectionRow AllPositiveNonConnectorFields where
  exactBlock :=
    AllPositiveNonConnectorFields.targetUpperConstructionFiveSixteenAt_exactBlock
  exactTarget :=
    AllPositiveNonConnectorFields.targetUpperConstructionFiveSixteen
  arbitraryTarget :=
    AllPositiveNonConnectorFields.targetUpperConstructionFiveSixteenArbitrary

def tableFamilyRow : ProjectionRow TableFamilyPackage where
  exactBlock := TableFamilyPackage.targetUpperConstructionFiveSixteenAt_exactBlock
  exactTarget := TableFamilyPackage.targetUpperConstructionFiveSixteen
  arbitraryTarget := TableFamilyPackage.targetUpperConstructionFiveSixteenArbitrary

def vectorRow : ProjectionRow VectorPackage where
  exactBlock := VectorPackage.targetUpperConstructionFiveSixteenAt_exactBlock
  exactTarget := VectorPackage.targetUpperConstructionFiveSixteen
  arbitraryTarget := VectorPackage.targetUpperConstructionFiveSixteenArbitrary

def listRow : ProjectionRow ListPackage where
  exactBlock := ListPackage.targetUpperConstructionFiveSixteenAt_exactBlock
  exactTarget := ListPackage.targetUpperConstructionFiveSixteen
  arbitraryTarget := ListPackage.targetUpperConstructionFiveSixteenArbitrary

/-- Checked W12 finite-certificate obligation matrix. -/
structure Matrix where
  rawFields : ProjectionRow AllPositiveNonConnectorFields
  nativeTables : ProjectionRow TableFamilyPackage
  vectorTables : ProjectionRow VectorPackage
  listTables : ProjectionRow ListPackage

def matrix : Matrix where
  rawFields := rawFieldsRow
  nativeTables := tableFamilyRow
  vectorTables := vectorRow
  listTables := listRow

theorem targetUpperConstructionFiveSixteen_of_rawFields
    (C : AllPositiveNonConnectorFields) :
    ExactTarget :=
  matrix.rawFields.exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_rawFields
    (C : AllPositiveNonConnectorFields) :
    ArbitraryTarget :=
  matrix.rawFields.arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_tableFamilyPackage
    (P : TableFamilyPackage) :
    ExactTarget :=
  matrix.nativeTables.exactTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_tableFamilyPackage
    (P : TableFamilyPackage) :
    ArbitraryTarget :=
  matrix.nativeTables.arbitraryTarget P

theorem targetUpperConstructionFiveSixteen_of_vectorPackage
    (P : VectorPackage) :
    ExactTarget :=
  matrix.vectorTables.exactTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_vectorPackage
    (P : VectorPackage) :
    ArbitraryTarget :=
  matrix.vectorTables.arbitraryTarget P

theorem targetUpperConstructionFiveSixteen_of_listPackage
    (P : ListPackage) :
    ExactTarget :=
  matrix.listTables.exactTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_listPackage
    (P : ListPackage) :
    ArbitraryTarget :=
  matrix.listTables.arbitraryTarget P

end

end FiniteCertificateObligationsW12
end PachToth
end ErdosProblems1066
