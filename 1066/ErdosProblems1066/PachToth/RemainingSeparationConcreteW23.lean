import ErdosProblems1066.PachToth.RemainingSeparationInhabitationW22
import ErdosProblems1066.PachToth.ConcreteValueMatrixFamilyInhabitationW22
import ErdosProblems1066.PachToth.ConcreteCrossBlockInputPackageW22
import ErdosProblems1066.PachToth.GeneratedPolynomialCertificateW21

set_option autoImplicit false

/-!
# W23 concrete remaining-separation closure

This file names the exact row package equivalent to the W21 remaining
separation field and records the concrete row routes into it.  The final
field is closed through the W22 role-hinged source obstruction.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RemainingSeparationConcreteW23

noncomputable section

abbrev RoleHingedPeriodSearchFamily : Type :=
  ReducedMetricSourceFieldsW21.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex : Type :=
  RemainingSeparationInhabitationW22.LocalVertexIndex

abbrev RemainingSeparationField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ReducedMetricSourceFieldsW21.RemainingSeparationField F

abbrev ExactRemainingSeparationPackage
    (F : RoleHingedPeriodSearchFamily) : Type :=
  RemainingSeparationInhabitationW22.CrossBlockLowerBounds F

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixFamily

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteCrossBlockInputPackageW22.ConcreteNonConnectorLowerTableFamily

abbrev GeneratedPointPolynomialCertificateFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily F

abbrev GeneratedPointValueCertificateFamily
    (F : RoleHingedPeriodSearchFamily) : Type :=
  PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily F

def exactPackageOfRemainingSeparation
    {F : RoleHingedPeriodSearchFamily}
    (separated : RemainingSeparationField F) :
    ExactRemainingSeparationPackage F :=
  RemainingSeparationInhabitationW22.crossBlockLowerBoundsOfRemainingSeparation
    separated

def remainingSeparationFieldOfExactPackage
    {F : RoleHingedPeriodSearchFamily}
    (P : ExactRemainingSeparationPackage F) :
    RemainingSeparationField F :=
  RemainingSeparationInhabitationW22.remainingSeparationOfCrossBlockLowerBounds
    P

theorem nonempty_exactPackage_iff_remainingSeparationField
    (F : RoleHingedPeriodSearchFamily) :
    Nonempty (ExactRemainingSeparationPackage F) <->
      RemainingSeparationField F :=
  RemainingSeparationInhabitationW22.nonempty_crossBlockLowerBounds_iff_remainingSeparation
    F

theorem remainingSeparationField_iff_nonempty_exactPackage
    (F : RoleHingedPeriodSearchFamily) :
    RemainingSeparationField F <->
      Nonempty (ExactRemainingSeparationPackage F) :=
  (nonempty_exactPackage_iff_remainingSeparationField F).symm

def exactPackageOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ExactRemainingSeparationPackage C.toRoleHingedPeriodSearchFamily :=
  exactPackageOfRemainingSeparation
    (RemainingSeparationInhabitationW22.remainingSeparationOfConcreteValueMatrixFamily
      C)

def exactPackageOfConcreteValueMatrixRows
    (P : ConcreteValueMatrixRowPackage) :
    ExactRemainingSeparationPackage
      P.periodSearch.toRoleHingedPeriodSearchFamily :=
  exactPackageOfConcreteValueMatrixFamily P.toConcreteValueMatrixFamily

theorem remainingSeparationFieldOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    RemainingSeparationField C.toRoleHingedPeriodSearchFamily :=
  remainingSeparationFieldOfExactPackage
    (exactPackageOfConcreteValueMatrixFamily C)

theorem remainingSeparationFieldOfConcreteValueMatrixRows
    (P : ConcreteValueMatrixRowPackage) :
    RemainingSeparationField
      P.periodSearch.toRoleHingedPeriodSearchFamily :=
  remainingSeparationFieldOfExactPackage
    (exactPackageOfConcreteValueMatrixRows P)

def exactPackageOfConcreteLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactRemainingSeparationPackage C.toRoleHingedPeriodSearchFamily :=
  C.toCrossBlockLowerBounds

def inputPackageOfConcreteLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    ConcreteCrossBlockInputPackageW22.W19InputPackage :=
  ConcreteCrossBlockInputPackageW22.inputPackageOfConcreteNonConnectorLowerTableFamily
    C

theorem remainingSeparationFieldOfConcreteLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    RemainingSeparationField C.toRoleHingedPeriodSearchFamily :=
  remainingSeparationFieldOfExactPackage
    (exactPackageOfConcreteLowerTableFamily C)

def exactPackageOfGeneratedPointPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : GeneratedPointPolynomialCertificateFamily F) :
    ExactRemainingSeparationPackage F :=
  exactPackageOfRemainingSeparation
    (RemainingSeparationInhabitationW22.remainingSeparationOfGeneratedPointPolynomialCertificateFamily
      C)

def exactPackageOfGeneratedPointValueCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : GeneratedPointValueCertificateFamily F) :
    ExactRemainingSeparationPackage F :=
  exactPackageOfRemainingSeparation
    (RemainingSeparationInhabitationW22.remainingSeparationOfGeneratedPointValueCertificateFamily
      C)

def exactPackageOfGeneratedPointPolynomialFacts
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
    ExactRemainingSeparationPackage F :=
  exactPackageOfRemainingSeparation
    (RemainingSeparationInhabitationW22.remainingSeparationOfGeneratedPointPolynomialFacts
      F polynomial_ge_one_lt)

theorem remainingSeparationFieldOfGeneratedPointPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : GeneratedPointPolynomialCertificateFamily F) :
    RemainingSeparationField F :=
  remainingSeparationFieldOfExactPackage
    (exactPackageOfGeneratedPointPolynomialCertificateFamily C)

theorem remainingSeparationFieldOfGeneratedPointValueCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : GeneratedPointValueCertificateFamily F) :
    RemainingSeparationField F :=
  remainingSeparationFieldOfExactPackage
    (exactPackageOfGeneratedPointValueCertificateFamily C)

theorem remainingSeparationFieldOfGeneratedPointPolynomialFacts
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
  remainingSeparationFieldOfExactPackage
    (exactPackageOfGeneratedPointPolynomialFacts F polynomial_ge_one_lt)

def closedExactPackage
    (F : RoleHingedPeriodSearchFamily) :
    ExactRemainingSeparationPackage F :=
  exactPackageOfRemainingSeparation
    (RemainingSeparationInhabitationW22.remainingSeparation_of_roleHingedPeriodSearchNoGo
      F)

theorem remainingSeparationField_closed
    (F : RoleHingedPeriodSearchFamily) :
    RemainingSeparationField F :=
  remainingSeparationFieldOfExactPackage (closedExactPackage F)

end

end RemainingSeparationConcreteW23
end PachToth

namespace Verified

abbrev PachTothW23RemainingSeparationPackage
    (F : PachToth.RemainingSeparationConcreteW23.RoleHingedPeriodSearchFamily) :
    Type :=
  PachToth.RemainingSeparationConcreteW23.ExactRemainingSeparationPackage F

theorem pachtoth_w23_remainingSeparationField_closed
    (F : PachToth.RemainingSeparationConcreteW23.RoleHingedPeriodSearchFamily) :
    PachToth.RemainingSeparationConcreteW23.RemainingSeparationField F :=
  PachToth.RemainingSeparationConcreteW23.remainingSeparationField_closed F

theorem pachtoth_w23_remainingSeparationField_iff_exactPackage
    (F : PachToth.RemainingSeparationConcreteW23.RoleHingedPeriodSearchFamily) :
    PachToth.RemainingSeparationConcreteW23.RemainingSeparationField F <->
      Nonempty (PachTothW23RemainingSeparationPackage F) :=
  PachToth.RemainingSeparationConcreteW23.remainingSeparationField_iff_nonempty_exactPackage
    F

end Verified
end ErdosProblems1066
