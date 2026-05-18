import ErdosProblems1066.PachToth.PachTothW23RouteAudit
import ErdosProblems1066.PachToth.RemainingSeparationConcreteW23
import ErdosProblems1066.PachToth.DirectCrossBlockInputPackageW24
import ErdosProblems1066.PachToth.FullMetricClosedPlacementW24

set_option autoImplicit false

/-!
# W25 same-family reduced metric fields

This file isolates the fixed-family handoff into
`PachTothW23RouteAudit.ReducedMetricFields F`.  The key point is that the
generated-chain family parameter is never repackaged: generic constructors use
the input `F`, and role-hinged/concrete constructors target exactly the
role-hinged generated family supplied by W21/W23.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ReducedMetricFieldsSameFamilyW25

open FiniteGraph

noncomputable section

abbrev GeneratedChainFamily : Type :=
  PachTothW23RouteAudit.GeneratedChainFamily

abbrev ReducedMetricFields
    (F : GeneratedChainFamily) : Prop :=
  PachTothW23RouteAudit.ReducedMetricFields F

abbrev SeparationField
    (F : GeneratedChainFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    ReducedMetricHypothesesProducerW20.GeneratedGlobalSeparationAt F k hk

abbrev BaseSameBlockField
    (F : GeneratedChainFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
      (F.base k hk)

abbrev TransitionSameBlockField
    (F : GeneratedChainFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      (F.O k hk)

def fieldsOfSameFamilyData
    {F : GeneratedChainFamily}
    (separated : SeparationField F)
    (baseSame : BaseSameBlockField F)
    (transitionSame : TransitionSameBlockField F) :
    ReducedMetricFields F where
  separated := separated
  base_same_block_isometry := baseSame
  transition_preserves_same_block_distances := transitionSame

@[simp]
theorem fieldsOfSameFamilyData_separated
    {F : GeneratedChainFamily}
    (separated : SeparationField F)
    (baseSame : BaseSameBlockField F)
    (transitionSame : TransitionSameBlockField F) :
    (fieldsOfSameFamilyData separated baseSame transitionSame).separated =
      separated := by
  rfl

@[simp]
theorem fieldsOfSameFamilyData_baseSame
    {F : GeneratedChainFamily}
    (separated : SeparationField F)
    (baseSame : BaseSameBlockField F)
    (transitionSame : TransitionSameBlockField F) :
    (fieldsOfSameFamilyData separated baseSame transitionSame).base_same_block_isometry =
      baseSame := by
  rfl

@[simp]
theorem fieldsOfSameFamilyData_transitionSame
    {F : GeneratedChainFamily}
    (separated : SeparationField F)
    (baseSame : BaseSameBlockField F)
    (transitionSame : TransitionSameBlockField F) :
    (fieldsOfSameFamilyData separated baseSame transitionSame).transition_preserves_same_block_distances =
      transitionSame := by
  rfl

def sameFamilyDataOfFields
    {F : GeneratedChainFamily}
    (D : ReducedMetricFields F) :
    SeparationField F /\ BaseSameBlockField F /\ TransitionSameBlockField F :=
  And.intro D.separated
    (And.intro D.base_same_block_isometry
      D.transition_preserves_same_block_distances)

theorem nonempty_reducedMetricFields_iff_sameFamilyData
    (F : GeneratedChainFamily) :
    Nonempty (ReducedMetricFields F) <->
      SeparationField F /\ BaseSameBlockField F /\ TransitionSameBlockField F := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact sameFamilyDataOfFields D
  case mpr =>
    intro h
    exact
      Nonempty.intro
        (fieldsOfSameFamilyData h.1 h.2.1 h.2.2)

def reducedMetricHypothesesOfFields
    {F : GeneratedChainFamily}
    (D : ReducedMetricFields F) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F :=
  D.toReducedMetricHypotheses

/-! ## Role-hinged W21/W23 remaining-separation routes -/

abbrev RoleHingedPeriodSearchFamily : Type :=
  ReducedMetricSourceFieldsW21.RoleHingedPeriodSearchFamily

abbrev roleHingedGeneratedChainFamily
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedChainFamily :=
  ReducedMetricSourceFieldsW21.roleHingedGeneratedChainFamily F

abbrev RemainingSeparationField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ReducedMetricSourceFieldsW21.RemainingSeparationField F

abbrev ExactRemainingSeparationPackage
    (F : RoleHingedPeriodSearchFamily) : Type :=
  RemainingSeparationConcreteW23.ExactRemainingSeparationPackage F

def fieldsOfRemainingSeparation
    (F : RoleHingedPeriodSearchFamily)
    (separated : RemainingSeparationField F) :
    ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  ReducedMetricSourceFieldsW21.fieldsOfSeparation F separated

@[simp]
theorem fieldsOfRemainingSeparation_separated
    (F : RoleHingedPeriodSearchFamily)
    (separated : RemainingSeparationField F) :
    ReducedMetricSourceFieldsW21.separationOfFields
      (fieldsOfRemainingSeparation F separated) =
        separated := by
  rfl

theorem nonempty_roleHingedReducedMetricFields_iff_remainingSeparation
    (F : RoleHingedPeriodSearchFamily) :
    Nonempty (ReducedMetricFields (roleHingedGeneratedChainFamily F)) <->
      RemainingSeparationField F :=
  ReducedMetricSourceFieldsW21.nonempty_reducedMetricFields_iff_remainingSeparation
    F

def fieldsOfExactRemainingSeparationPackage
    {F : RoleHingedPeriodSearchFamily}
    (P : ExactRemainingSeparationPackage F) :
    ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  fieldsOfRemainingSeparation F
    (RemainingSeparationConcreteW23.remainingSeparationFieldOfExactPackage P)

theorem nonempty_roleHingedReducedMetricFields_iff_exactPackage
    (F : RoleHingedPeriodSearchFamily) :
    Nonempty (ReducedMetricFields (roleHingedGeneratedChainFamily F)) <->
      Nonempty (ExactRemainingSeparationPackage F) :=
  Iff.trans
    (nonempty_roleHingedReducedMetricFields_iff_remainingSeparation F)
    (RemainingSeparationConcreteW23.remainingSeparationField_iff_nonempty_exactPackage
      F)

def fieldsOfGeneratedPointPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : RemainingSeparationConcreteW23.GeneratedPointPolynomialCertificateFamily F) :
    ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  fieldsOfExactRemainingSeparationPackage
    (RemainingSeparationConcreteW23.exactPackageOfGeneratedPointPolynomialCertificateFamily
      C)

def fieldsOfGeneratedPointValueCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : RemainingSeparationConcreteW23.GeneratedPointValueCertificateFamily F) :
    ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  fieldsOfExactRemainingSeparationPackage
    (RemainingSeparationConcreteW23.exactPackageOfGeneratedPointValueCertificateFamily
      C)

def fieldsOfGeneratedPointPolynomialFacts
    (F : RoleHingedPeriodSearchFamily)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : RemainingSeparationConcreteW23.LocalVertexIndex)
        (j : Fin k) (v : RemainingSeparationConcreteW23.LocalVertexIndex),
          i.val < j.val ->
            Not (GeneratedPolynomialCertificateW21.IndexedCyclicConnectorPair
              hk i u j v) ->
              1 <=
                GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
                  F hk i u j v) :
    ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  fieldsOfExactRemainingSeparationPackage
    (RemainingSeparationConcreteW23.exactPackageOfGeneratedPointPolynomialFacts
      F polynomial_ge_one_lt)

def fieldsOfConcreteValueMatrixFamily
    (C : RemainingSeparationConcreteW23.ConcreteValueMatrixFamily) :
    ReducedMetricFields
      (roleHingedGeneratedChainFamily C.toRoleHingedPeriodSearchFamily) :=
  fieldsOfExactRemainingSeparationPackage
    (RemainingSeparationConcreteW23.exactPackageOfConcreteValueMatrixFamily C)

def fieldsOfConcreteValueMatrixRows
    (P : RemainingSeparationConcreteW23.ConcreteValueMatrixRowPackage) :
    ReducedMetricFields
      (roleHingedGeneratedChainFamily
        P.periodSearch.toRoleHingedPeriodSearchFamily) :=
  fieldsOfExactRemainingSeparationPackage
    (RemainingSeparationConcreteW23.exactPackageOfConcreteValueMatrixRows P)

def fieldsOfConcreteLowerTableFamily
    (C : RemainingSeparationConcreteW23.ConcreteNonConnectorLowerTableFamily) :
    ReducedMetricFields
      (roleHingedGeneratedChainFamily C.toRoleHingedPeriodSearchFamily) :=
  fieldsOfExactRemainingSeparationPackage
    (RemainingSeparationConcreteW23.exactPackageOfConcreteLowerTableFamily C)

/-! ## W24 direct and full-metric compatible adapters -/

def fieldsOfW20SourceFields
    (S : GeneratedChainFamilyProducerW20.SourceFields) :
    ReducedMetricFields S.family :=
  GeneratedChainSourceFieldsInhabitationW22.reducedMetricFieldsOfSourceFields S

def fieldsOfDirectReducedSourceFieldsOver
    {C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily}
    (D : DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOver C) :
    ReducedMetricFields D.toSourceFields.family :=
  fieldsOfW20SourceFields D.toSourceFields

def fieldsOfDirectReducedSourceFieldsOfBareLowerTables
    {F : DirectCrossBlockInputPackageW24.RoleHingedPeriodSearchFamily}
    {T : DirectCrossBlockInputPackageW24.NonConnectorLowerTableFamily F}
    (D : DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOfBareLowerTables T) :
    ReducedMetricFields D.toSourceFields.family :=
  fieldsOfW20SourceFields D.toSourceFields

abbrev ExactBaseFullMetricCoreFields : Type :=
  ExactBaseFullMetricConcreteW23.ExactBaseFullMetricCoreFields

abbrev ExactBaseRemainingSeparationField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  ExactBaseFullMetricConcreteW23.RemainingSeparationField C

abbrev ExactBaseReducedTransitionField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
    C.O

def fieldsOfExactBaseSeparationAndReducedTransition
    (C : ExactBaseFullMetricCoreFields)
    (separated : ExactBaseRemainingSeparationField C)
    (transitionSame : ExactBaseReducedTransitionField C) :
    ReducedMetricFields C.family :=
  fieldsOfSameFamilyData
    (fun k hk => separated k hk)
    (fun _k _hk =>
      GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry)
    (fun _k _hk => transitionSame)

def fieldsOfExactBaseConcreteCoreAndReducedTransition
    (D : ExactBaseFullMetricConcreteW23.ExactBaseFullMetricConcreteCoreFields)
    (transitionSame : ExactBaseReducedTransitionField D.core) :
    ReducedMetricFields D.core.family :=
  fieldsOfExactBaseSeparationAndReducedTransition
    D.core D.separated transitionSame

def reducedWitnessOfSameFamilyFields
    {F : GeneratedChainFamily}
    (closure : FullMetricClosedPlacementW24.GeneratedChainFamilyClosures F)
    (D : ReducedMetricFields F) :
    FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness where
  family := F
  closure := closure
  metric := D.toReducedMetricHypotheses

end

end ReducedMetricFieldsSameFamilyW25
end PachToth
end ErdosProblems1066
