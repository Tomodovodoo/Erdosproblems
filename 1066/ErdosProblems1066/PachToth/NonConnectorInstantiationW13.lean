import ErdosProblems1066.PachToth.NonConnectorSeparationW12
import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix
import ErdosProblems1066.PachToth.FiniteCertificateObligationsW12
import ErdosProblems1066.PachToth.GeneratedPolynomialLowerTableRoute

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace NonConnectorInstantiationW13

open FiniteGraph
open NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTable

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  NonConnectorSeparationW12.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  NonConnectorSeparationW12.LocalVertexIndex

abbrev GeneratedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Prop :=
  NonConnectorSeparationW12.GeneratedCyclicConnectorPair hk i u j v

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  NonConnectorSeparationW12.IndexedCyclicConnectorPair hk i u j v

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev GeneratedNonConnectorSqDistanceTable :=
  NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTable

abbrev GeneratedNonConnectorSqDistanceTableFamily :=
  NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily

def onePositive : 0 < 1 :=
  Nat.zero_lt_succ 0

theorem finOne_not_ne (i j : Fin 1) : Not (Ne i j) := by
  intro hij
  exact hij (Subsingleton.elim i j)

def lengthOneGeneratedNonConnectorSqDistanceTable
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedNonConnectorSqDistanceTable F 1 onePositive :=
  NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTable.ofSqDistGeOne
    (F := F) (k := 1) (hk := onePositive) (by
      intro i _u j _v hij _hnot_connector
      exact False.elim (finOne_not_ne i j hij))

def lengthOneIndexedNonConnectorCrossBlockSqDistanceTable
    (F : RoleHingedPeriodSearchFamily) :
    IndexedNonConnectorCrossBlockSqDistanceTable F 1 onePositive :=
  (lengthOneGeneratedNonConnectorSqDistanceTable F).toIndexedNonConnectorCrossBlockSqDistanceTable

theorem lengthOne_generatedGlobalSeparation
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      onePositive
      BaseTransitionRealization.exactBase
      (F.orientation 1 onePositive) :=
  (lengthOneGeneratedNonConnectorSqDistanceTable F).generatedGlobalSeparation

def generatedTableFamilyOfIndexedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    GeneratedNonConnectorSqDistanceTableFamily F where
  table := fun k hk =>
    ofIndexedNonConnectorCrossBlockSqDistanceTable (T.table k hk)

theorem generatedTableFamilyOfIndexedTableFamily_separated
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  (generatedTableFamilyOfIndexedTableFamily T).separated k hk

theorem targetUpperConstructionFiveSixteen_ofIndexedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (generatedTableFamilyOfIndexedTableFamily T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_ofIndexedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (generatedTableFamilyOfIndexedTableFamily T).targetUpperConstructionFiveSixteenArbitrary

structure IndexedSqDistanceFields
    (F : RoleHingedPeriodSearchFamily) where
  sqDist_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <=
              CrossBlockDistanceSqReduction.indexedGeneratedSqDist
                F hk i u j v

namespace IndexedSqDistanceFields

def toIndexedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedSqDistanceFields F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    { sqDist_ge_one := D.sqDist_ge_one k hk }

def toGeneratedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedSqDistanceFields F) :
    GeneratedNonConnectorSqDistanceTableFamily F :=
  generatedTableFamilyOfIndexedTableFamily D.toIndexedTableFamily

theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedSqDistanceFields F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  D.toGeneratedTableFamily.separated k hk

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedSqDistanceFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toGeneratedTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedSqDistanceFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  D.toGeneratedTableFamily.targetUpperConstructionFiveSixteenArbitrary

end IndexedSqDistanceFields

structure IndexedValueFields
    (F : RoleHingedPeriodSearchFamily) where
  value :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_sqDist :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            value k hk i u j v =
              CrossBlockDistanceSqReduction.indexedGeneratedSqDist
                F hk i u j v
  value_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= value k hk i u j v

namespace IndexedValueFields

def toSqDistanceFields
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedValueFields F) :
    IndexedSqDistanceFields F where
  sqDist_ge_one := by
    intro k hk i u j v hij hnot_connector
    simpa [D.value_eq_sqDist k hk i u j v hij hnot_connector] using
      D.value_ge_one k hk i u j v hij hnot_connector

def toIndexedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedValueFields F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  D.toSqDistanceFields.toIndexedTableFamily

def toGeneratedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedValueFields F) :
    GeneratedNonConnectorSqDistanceTableFamily F :=
  D.toSqDistanceFields.toGeneratedTableFamily

theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedValueFields F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  D.toGeneratedTableFamily.separated k hk

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toGeneratedTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (D : IndexedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  D.toGeneratedTableFamily.targetUpperConstructionFiveSixteenArbitrary

end IndexedValueFields

def generatedTableFamilyOfSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily F) :
    GeneratedNonConnectorSqDistanceTableFamily F :=
  generatedTableFamilyOfIndexedTableFamily T.toNonConnectorSqDistanceTableFamily

theorem targetUpperConstructionFiveSixteen_ofSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (generatedTableFamilyOfSqValueTableFamily T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_ofSqValueTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (generatedTableFamilyOfSqValueTableFamily T).targetUpperConstructionFiveSixteenArbitrary

def generatedTableFamilyOfValueMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (M : ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily F) :
    GeneratedNonConnectorSqDistanceTableFamily F :=
  generatedTableFamilyOfIndexedTableFamily M.toNonConnectorSqDistanceTableFamily

theorem targetUpperConstructionFiveSixteen_ofValueMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (M : ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (generatedTableFamilyOfValueMatrixFamily M).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_ofValueMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (M : ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (generatedTableFamilyOfValueMatrixFamily M).targetUpperConstructionFiveSixteenArbitrary

def generatedTableFamilyOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    GeneratedNonConnectorSqDistanceTableFamily C.toRoleHingedPeriodSearchFamily :=
  generatedTableFamilyOfValueMatrixFamily C.matrices

theorem targetUpperConstructionFiveSixteen_ofConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (generatedTableFamilyOfConcreteValueMatrixFamily C).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_ofConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (generatedTableFamilyOfConcreteValueMatrixFamily C).targetUpperConstructionFiveSixteenArbitrary

def generatedTableFamilyOfW12TableFamilyPackage
    (P : FiniteCertificateObligationsW12.TableFamilyPackage) :
    GeneratedNonConnectorSqDistanceTableFamily
      P.period.toRoleHingedPeriodSearchFamily :=
  generatedTableFamilyOfSqValueTableFamily P.tableFamily

theorem targetUpperConstructionFiveSixteen_ofW12TableFamilyPackage
    (P : FiniteCertificateObligationsW12.TableFamilyPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (generatedTableFamilyOfW12TableFamilyPackage P).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_ofW12TableFamilyPackage
    (P : FiniteCertificateObligationsW12.TableFamilyPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (generatedTableFamilyOfW12TableFamilyPackage P).targetUpperConstructionFiveSixteenArbitrary

def generatedTableFamilyOfGeneratedPointPolynomialFamily
    {F : RoleHingedPeriodSearchFamily}
    (T :
      GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTableFamily
        F) :
    GeneratedNonConnectorSqDistanceTableFamily F :=
  generatedTableFamilyOfIndexedTableFamily T.toNonConnectorSqDistanceTableFamily

theorem targetUpperConstructionFiveSixteen_ofGeneratedPointPolynomialFamily
    {F : RoleHingedPeriodSearchFamily}
    (T :
      GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTableFamily
        F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (generatedTableFamilyOfGeneratedPointPolynomialFamily T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_ofGeneratedPointPolynomialFamily
    {F : RoleHingedPeriodSearchFamily}
    (T :
      GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTableFamily
        F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (generatedTableFamilyOfGeneratedPointPolynomialFamily T)
    |>.targetUpperConstructionFiveSixteenArbitrary

end

end NonConnectorInstantiationW13
end PachToth
end ErdosProblems1066
