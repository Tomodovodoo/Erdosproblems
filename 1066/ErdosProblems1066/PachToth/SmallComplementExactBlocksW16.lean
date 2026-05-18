import ErdosProblems1066.PachToth.LargeThresholdSmallCasesW15
import ErdosProblems1066.PachToth.ExactBlockCertificateW13
import ErdosProblems1066.PachToth.FiniteCertificateInstantiationW13

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace SmallComplementExactBlocksW16

noncomputable section

open SmallCaseCertificates
open ExactBlockCertificateW13

abbrev SmallComplement (K0 : Nat) : Prop :=
  LargeThresholdSmallCasesW15.SmallComplement K0

abbrev AllPositiveFields :=
  FiniteCertificateInstantiationW13.W12.AllPositiveNonConnectorFields

abbrev ConcreteValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily

def pt7K0 : Nat := 7

theorem targetUpperConstructionFiveSixteenSmallUpTo_of_allPositiveFields
    (K0 : Nat) (F : AllPositiveFields) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * K0) := by
  exact
    targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
      K0
      (fun k _hklt hk =>
        F.targetUpperConstructionFiveSixteenAt_exactBlock k hk)

theorem smallComplement_of_allPositiveFields
    (K0 : Nat) (F : AllPositiveFields) :
    SmallComplement K0 :=
  targetUpperConstructionFiveSixteenSmallUpTo_of_allPositiveFields K0 F

theorem targetUpperConstructionFiveSixteenSmallUpTo_pt7_of_allPositiveFields
    (F : AllPositiveFields) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * pt7K0) :=
  targetUpperConstructionFiveSixteenSmallUpTo_of_allPositiveFields pt7K0 F

theorem smallComplement_pt7_of_allPositiveFields
    (F : AllPositiveFields) :
    SmallComplement pt7K0 :=
  smallComplement_of_allPositiveFields pt7K0 F

theorem targetUpperConstructionFiveSixteenSmallUpTo_of_concreteValueMatrixFamily
    (K0 : Nat) (C : ConcreteValueMatrixFamily) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * K0) :=
  targetUpperConstructionFiveSixteenSmallUpTo_of_allPositiveFields K0
    (FiniteCertificateInstantiationW13.fieldsOfConcreteValueMatrixFamily C)

theorem smallComplement_of_concreteValueMatrixFamily
    (K0 : Nat) (C : ConcreteValueMatrixFamily) :
    SmallComplement K0 :=
  targetUpperConstructionFiveSixteenSmallUpTo_of_concreteValueMatrixFamily K0 C

theorem smallComplement_pt7_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    SmallComplement pt7K0 :=
  smallComplement_of_concreteValueMatrixFamily pt7K0 C

theorem targetUpperConstructionFiveSixteenSmallUpTo_of_candidateValueMatrixFamily
    (K0 : Nat) (C : CandidateValueMatrixFamily) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * K0) :=
  targetUpperConstructionFiveSixteenSmallUpTo_of_allPositiveFields K0
    (FiniteCertificateInstantiationW13.fieldsOfCandidateValueMatrixFamily C)

theorem smallComplement_of_candidateValueMatrixFamily
    (K0 : Nat) (C : CandidateValueMatrixFamily) :
    SmallComplement K0 :=
  targetUpperConstructionFiveSixteenSmallUpTo_of_candidateValueMatrixFamily K0 C

theorem smallComplement_pt7_of_candidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    SmallComplement pt7K0 :=
  smallComplement_of_candidateValueMatrixFamily pt7K0 C

theorem targetUpperConstructionFiveSixteenSmallUpTo_two_of_concreteOneBlockCertificate
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * 2) := by
  exact
    targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
      2
      (fun k hklt hk => by
        have hkone : k = 1 := by
          omega
        subst k
        simpa using
          targetUpperConstructionFiveSixteenAt_of_concreteOneBlockCertificate C)

theorem smallComplement_two_of_concreteOneBlockCertificate
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation) :
    SmallComplement 2 :=
  targetUpperConstructionFiveSixteenSmallUpTo_two_of_concreteOneBlockCertificate C

end

end SmallComplementExactBlocksW16
end PachToth
end ErdosProblems1066
