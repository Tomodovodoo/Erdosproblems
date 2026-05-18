import ErdosProblems1066.PachToth.ReducedMetricSourceFieldsW21
import ErdosProblems1066.PachToth.IndexedCrossBlockTableConcrete
import ErdosProblems1066.PachToth.GeneratedPolynomialCertificateW21
import ErdosProblems1066.PachToth.ConcreteValueMatrixToInputPackageW21
import ErdosProblems1066.PachToth.ExactBaseSourceNoGoW21

set_option autoImplicit false

/-!
# W22 remaining separation inhabitation

This module isolates the last reduced-metric source field for the
role-hinged generated family.  It gives direct constructors from the W19
separation route, generated and indexed non-connector tables, cross-block
lower rows, polynomial certificates, and value certificates.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RemainingSeparationInhabitationW22

open FiniteGraph

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  ReducedMetricSourceFieldsW21.RoleHingedPeriodSearchFamily

abbrev RemainingSeparationField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ReducedMetricSourceFieldsW21.RemainingSeparationField F

abbrev RoleHingedGeneratedChainFamily
    (F : RoleHingedPeriodSearchFamily) :=
  ReducedMetricSourceFieldsW21.roleHingedGeneratedChainFamily F

abbrev ReducedMetricFields
    (F : RoleHingedPeriodSearchFamily) :=
  ReducedMetricHypothesesProducerW20.ReducedMetricFields
    (RoleHingedGeneratedChainFamily F)

abbrev GeneratedPointAt
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :=
  ReducedMetricHypothesesProducerW20.GeneratedPointAt
    (RoleHingedGeneratedChainFamily F) k hk

abbrev GeneratedGlobalSeparationAt
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  ReducedMetricHypothesesProducerW20.GeneratedGlobalSeparationAt
    (RoleHingedGeneratedChainFamily F) k hk

abbrev CrossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) :=
  NonConnectorSeparationW12.CrossBlockLowerBounds F

abbrev IndexedCrossBlockLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTableFamily F

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTableFamily F

abbrev GeneratedNonConnectorSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily F

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

/-! ## Exact reduced-metric and W19 reductions -/

def reducedMetricFieldsOfRemainingSeparation
    {F : RoleHingedPeriodSearchFamily}
    (separated : RemainingSeparationField F) :
    ReducedMetricFields F :=
  ReducedMetricSourceFieldsW21.fieldsOfSeparation F separated

def remainingSeparationOfReducedMetricFields
    {F : RoleHingedPeriodSearchFamily}
    (D : ReducedMetricFields F) :
    RemainingSeparationField F :=
  ReducedMetricSourceFieldsW21.separationOfFields D

theorem remainingSeparation_iff_nonempty_reducedMetricFields
    (F : RoleHingedPeriodSearchFamily) :
    RemainingSeparationField F <-> Nonempty (ReducedMetricFields F) :=
  (ReducedMetricSourceFieldsW21.nonempty_reducedMetricFields_iff_remainingSeparation
    F).symm

/-- W19 separation rows whose point map is the generated role-hinged point
map. -/
structure W19GeneratedSeparationRows
    (F : RoleHingedPeriodSearchFamily) where
  separation : ClosedPlacementSeparationW19.SeparationFamilyCertificate
  point_eq :
    forall (k : Nat) (hk : 0 < k),
      separation.point k hk = GeneratedPointAt F k hk

def w19RowsOfRemainingSeparation
    {F : RoleHingedPeriodSearchFamily}
    (separated : RemainingSeparationField F) :
    W19GeneratedSeparationRows F where
  separation :=
    { point := fun k hk => GeneratedPointAt F k hk
      separated := fun k hk => separated k hk }
  point_eq := by
    intro _k _hk
    rfl

def remainingSeparationOfW19Rows
    {F : RoleHingedPeriodSearchFamily}
    (R : W19GeneratedSeparationRows F) :
    RemainingSeparationField F :=
  remainingSeparationOfReducedMetricFields
    (ReducedMetricSourceFieldsW21.fieldsOfW19SeparationFamily
      R.separation R.point_eq)

theorem nonempty_w19Rows_iff_remainingSeparation
    (F : RoleHingedPeriodSearchFamily) :
    Nonempty (W19GeneratedSeparationRows F) <->
      RemainingSeparationField F := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact remainingSeparationOfW19Rows R
  case mpr =>
    intro h
    exact Nonempty.intro (w19RowsOfRemainingSeparation h)

/-! ## Cross-block lower-row equivalences -/

def crossBlockLowerBoundsOfRemainingSeparation
    {F : RoleHingedPeriodSearchFamily}
    (separated : RemainingSeparationField F) :
    CrossBlockLowerBounds F where
  lower := fun _k _hk _i _u _j _v => 1
  lower_ge_one := by
    intro _k _hk _i _u _j _v _hij
    exact le_rfl
  lower_bound := by
    intro k hk i u j v hij
    have hpair : Ne (i, u) (j, v) := by
      intro hp
      exact hij (congrArg Prod.fst hp)
    simpa using separated k hk i u j v hpair

def remainingSeparationOfCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F) :
    RemainingSeparationField F :=
  fun k hk => H.separated k hk

theorem nonempty_crossBlockLowerBounds_iff_remainingSeparation
    (F : RoleHingedPeriodSearchFamily) :
    Nonempty (CrossBlockLowerBounds F) <->
      RemainingSeparationField F := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact remainingSeparationOfCrossBlockLowerBounds H
  case mpr =>
    intro h
    exact Nonempty.intro (crossBlockLowerBoundsOfRemainingSeparation h)

def indexedCrossBlockLowerTableFamilyOfRemainingSeparation
    {F : RoleHingedPeriodSearchFamily}
    (separated : RemainingSeparationField F) :
    IndexedCrossBlockLowerTableFamily F where
  table := fun k hk =>
    { lower := fun _i _u _j _v => 1
      lower_ge_one := by
        intro _i _u _j _v _hij
        exact le_rfl
      lower_bound := by
        intro i u j v hij
        have hpair :
            Ne
              (i, CrossBlockLowerBoundsInterface.localVertexOfIndex u)
              (j, CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
          intro hp
          exact hij (congrArg Prod.fst hp)
        simpa [CrossBlockLowerBoundsInterface.indexedGeneratedPoint] using
          separated k hk i
            (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
            j (CrossBlockLowerBoundsInterface.localVertexOfIndex v)
            hpair }

def remainingSeparationOfIndexedCrossBlockLowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F) :
    RemainingSeparationField F :=
  remainingSeparationOfCrossBlockLowerBounds
    (CrossBlockLowerBoundsInterface.CrossBlockLowerBounds.ofIndexedTables T)

theorem nonempty_indexedCrossBlockLowerTableFamily_iff_remainingSeparation
    (F : RoleHingedPeriodSearchFamily) :
    Nonempty (IndexedCrossBlockLowerTableFamily F) <->
      RemainingSeparationField F := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
        exact remainingSeparationOfIndexedCrossBlockLowerTableFamily T
  case mpr =>
    intro h
    exact Nonempty.intro (indexedCrossBlockLowerTableFamilyOfRemainingSeparation h)

/-! ## Generated and indexed table constructors -/

def remainingSeparationOfGeneratedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    RemainingSeparationField F :=
  fun k hk => T.separated k hk

def remainingSeparationOfIndexedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    RemainingSeparationField F :=
  remainingSeparationOfGeneratedTableFamily
    (NonConnectorInstantiationW13.generatedTableFamilyOfIndexedTableFamily T)

def remainingSeparationOfIndexedSqDistanceFacts
    {F : RoleHingedPeriodSearchFamily}
    (sqDist_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          Ne i j ->
            Not (IndexedCrossBlockTableConcrete.IndexedCyclicConnectorPair
              hk i u j v) ->
              1 <=
                CrossBlockDistanceSqReduction.indexedGeneratedSqDist
                  F hk i u j v) :
    RemainingSeparationField F :=
  remainingSeparationOfIndexedTableFamily
    (IndexedCrossBlockTableConcrete.indexedNonConnectorCrossBlockSqDistanceTableFamilyOfFacts
      sqDist_ge_one)

def remainingSeparationOfIndexedPolynomialFacts
    {F : RoleHingedPeriodSearchFamily}
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCrossBlockTableConcrete.IndexedCyclicConnectorPair
              hk i u j v) ->
              1 <=
                CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                  F hk i u j v) :
    RemainingSeparationField F :=
  remainingSeparationOfIndexedTableFamily
    (IndexedCrossBlockTableConcrete.indexedNonConnectorCrossBlockSqDistanceTableFamilyOfPolynomialFacts
      polynomial_ge_one_lt)

/-! ## Concrete lower-table constructors -/

def remainingSeparationOfNonConnectorLowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily F) :
    RemainingSeparationField F :=
  fun k hk => T.separated k hk

def remainingSeparationOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily) :
    RemainingSeparationField C.toRoleHingedPeriodSearchFamily :=
  fun k hk => C.separated k hk

/-! ## Polynomial and value-certificate constructors -/

def remainingSeparationOfPositionPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : NonConnectorPolynomialCertificates.PositionPolynomialCertificateFamily F) :
    RemainingSeparationField F :=
  remainingSeparationOfCrossBlockLowerBounds C.toCrossBlockLowerBounds

def remainingSeparationOfPositionValueCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : NonConnectorPolynomialCertificates.PositionValueCertificateFamily F) :
    RemainingSeparationField F :=
  remainingSeparationOfPositionPolynomialCertificateFamily
    C.toPositionPolynomialCertificateFamily

def remainingSeparationOfGeneratedPointPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily F) :
    RemainingSeparationField F :=
  fun k hk => C.separated k hk

def remainingSeparationOfGeneratedPointValueCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily F) :
    RemainingSeparationField F :=
  remainingSeparationOfGeneratedPointPolynomialCertificateFamily
    C.toGeneratedPointPolynomialCertificateFamily

def remainingSeparationOfGeneratedPointPolynomialFacts
    (F : RoleHingedPeriodSearchFamily)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (GeneratedPolynomialCertificateW21.IndexedCyclicConnectorPair
              hk i u j v) ->
              1 <=
                GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
                  F hk i u j v) :
    RemainingSeparationField F :=
  fun k hk =>
    GeneratedPolynomialCertificateW21.generatedGlobalSeparationOfGeneratedPointPolynomialFacts
      F polynomial_ge_one_lt k hk

def remainingSeparationOfNonConnectorValueMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (M : ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily F) :
    RemainingSeparationField F :=
  remainingSeparationOfCrossBlockLowerBounds M.toCrossBlockLowerBounds

def remainingSeparationOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    RemainingSeparationField C.toRoleHingedPeriodSearchFamily :=
  remainingSeparationOfCrossBlockLowerBounds C.toCrossBlockLowerBounds

def remainingSeparationOfCandidatePolynomialCertificateFamily
    (C : NonConnectorPolynomialCertificates.CandidatePolynomialCertificateFamily) :
    RemainingSeparationField C.toRoleHingedPeriodSearchFamily :=
  remainingSeparationOfPositionPolynomialCertificateFamily C.certificates

def remainingSeparationOfCandidateValueCertificateFamily
    (C : NonConnectorPolynomialCertificates.CandidateValueCertificateFamily) :
    RemainingSeparationField C.toRoleHingedPeriodSearchFamily :=
  remainingSeparationOfCandidatePolynomialCertificateFamily
    C.toCandidatePolynomialCertificateFamily

def remainingSeparationOfCandidateGeneratedPointPolynomialCertificateFamily
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointPolynomialCertificateFamily) :
    RemainingSeparationField C.toRoleHingedPeriodSearchFamily :=
  remainingSeparationOfGeneratedPointPolynomialCertificateFamily C.certificates

def remainingSeparationOfCandidateGeneratedPointValueCertificateFamily
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointValueCertificateFamily) :
    RemainingSeparationField C.toRoleHingedPeriodSearchFamily :=
  remainingSeparationOfCandidateGeneratedPointPolynomialCertificateFamily
    C.toCandidateGeneratedPointPolynomialCertificateFamily

def remainingSeparationOfConcreteGeneratedPointValueCertificateFamily
    (C :
      PolynomialCertificateExtraction.ConcreteGeneratedPointValueCertificateFamily) :
    RemainingSeparationField C.toRoleHingedPeriodSearchFamily :=
  remainingSeparationOfConcreteValueMatrixFamily C.toConcreteValueMatrixFamily

/-! ## Reduced-metric field constructors from the same rows -/

def reducedMetricFieldsOfCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F) :
    ReducedMetricFields F :=
  ReducedMetricSourceFieldsW21.fieldsOfCrossBlockLowerBounds H

def reducedMetricFieldsOfIndexedTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    ReducedMetricFields F :=
  ReducedMetricSourceFieldsW21.fieldsOfIndexedNonConnectorCrossBlockSqDistanceTableFamily
    T

def reducedMetricFieldsOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    ReducedMetricFields C.toRoleHingedPeriodSearchFamily :=
  ReducedMetricSourceFieldsW21.fieldsOfConcreteValueMatrixFamily C

theorem remainingSeparationOfConcreteValueMatrixFamily_eq_w21
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    remainingSeparationOfReducedMetricFields
      (reducedMetricFieldsOfConcreteValueMatrixFamily C) =
        remainingSeparationOfConcreteValueMatrixFamily C :=
  rfl

/-! ## Strong role-hinge source no-go facts -/

theorem false_of_roleHingedPeriodSearchFamily
    (F : RoleHingedPeriodSearchFamily) :
    False :=
  ExactBaseSourceNoGoW21.false_of_strongRoleHingeTransitions F.transitions

theorem not_nonempty_roleHingedPeriodSearchFamily :
    Not (Nonempty RoleHingedPeriodSearchFamily) := by
  intro h
  cases h with
  | intro F =>
      exact false_of_roleHingedPeriodSearchFamily F

theorem remainingSeparation_of_roleHingedPeriodSearchNoGo
    (F : RoleHingedPeriodSearchFamily) :
    RemainingSeparationField F := by
  exact False.elim (false_of_roleHingedPeriodSearchFamily F)

end

end RemainingSeparationInhabitationW22
end PachToth
end ErdosProblems1066
