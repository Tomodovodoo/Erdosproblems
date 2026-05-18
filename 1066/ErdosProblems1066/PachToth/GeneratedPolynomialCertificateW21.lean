import ErdosProblems1066.PachToth.PolynomialCertificateExtraction
import ErdosProblems1066.PachToth.ReducedMetricHypothesesProducerW20

set_option autoImplicit false

/-!
# W21 generated polynomial certificate adapters

This module is a thin handoff from the generated-point polynomial certificate
spelling to the two downstream metric interfaces:

* one-period `GeneratedGlobalSeparation`; and
* family-level `GeneratedChainFamily.ReducedMetricHypotheses`.

No numerical certificate data is introduced here.  When the input is still a
generated-point certificate, the lemmas below record the exact reduction to
the named non-connector polynomial/value certificate families.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedPolynomialCertificateW21

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  PolynomialCertificateExtraction.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  PolynomialCertificateExtraction.LocalVertexIndex

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  PolynomialCertificateExtraction.IndexedCyclicConnectorPair hk i u j v

abbrev GeneratedChainFamily :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) :=
  GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F

abbrev GeneratedGlobalSeparationAt
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  GeneratedSeparationInterface.GeneratedGlobalSeparation
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (F.orientation k hk)

abbrev generatedChainFamilyOfRoleHinged
    (F : RoleHingedPeriodSearchFamily) : GeneratedChainFamily :=
  ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F

/-! ## Exact reductions to named certificate families -/

def positionPolynomialCertificateFamilyOfGeneratedPoint
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily
        F) :
    NonConnectorPolynomialCertificates.PositionPolynomialCertificateFamily F :=
  C.toPositionPolynomialCertificateFamily

def positionValueCertificateFamilyOfGeneratedPoint
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily F) :
    NonConnectorPolynomialCertificates.PositionValueCertificateFamily F :=
  C.toPositionValueCertificateFamily

theorem positionPolynomialCertificateFamilyOfGeneratedPoint_eq
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily
        F) :
    positionPolynomialCertificateFamilyOfGeneratedPoint C =
      C.toPositionPolynomialCertificateFamily :=
  rfl

theorem positionValueCertificateFamilyOfGeneratedPoint_eq
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily F) :
    positionValueCertificateFamilyOfGeneratedPoint C =
      C.toPositionValueCertificateFamily :=
  rfl

def candidatePolynomialCertificateFamilyOfGeneratedPoint
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointPolynomialCertificateFamily) :
    NonConnectorPolynomialCertificates.CandidatePolynomialCertificateFamily :=
  C.toCandidatePolynomialCertificateFamily

def candidateValueCertificateFamilyOfGeneratedPoint
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointValueCertificateFamily) :
    NonConnectorPolynomialCertificates.CandidateValueCertificateFamily :=
  C.toCandidateValueCertificateFamily

theorem candidatePolynomialCertificateFamilyOfGeneratedPoint_eq
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointPolynomialCertificateFamily) :
    candidatePolynomialCertificateFamilyOfGeneratedPoint C =
      C.toCandidatePolynomialCertificateFamily :=
  rfl

theorem candidateValueCertificateFamilyOfGeneratedPoint_eq
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointValueCertificateFamily) :
    candidateValueCertificateFamilyOfGeneratedPoint C =
      C.toCandidateValueCertificateFamily :=
  rfl

/-! ## One-period global separation adapters -/

theorem generatedGlobalSeparationOfPositionPolynomialCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C :
      NonConnectorPolynomialCertificates.PositionPolynomialCertificate
        F k hk) :
    GeneratedGlobalSeparationAt F k hk :=
  C.toNonConnectorSqDistanceTable.generatedGlobalSeparation

theorem generatedGlobalSeparationOfPositionValueCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C :
      NonConnectorPolynomialCertificates.PositionValueCertificate
        F k hk) :
    GeneratedGlobalSeparationAt F k hk :=
  C.toNonConnectorSqDistanceTable.generatedGlobalSeparation

theorem generatedGlobalSeparationOfGeneratedPointPolynomialCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C :
      PolynomialCertificateExtraction.GeneratedPointPositionPolynomialCertificate
        F k hk) :
    GeneratedGlobalSeparationAt F k hk :=
  generatedGlobalSeparationOfPositionPolynomialCertificate
    C.toPositionPolynomialCertificate

theorem generatedGlobalSeparationOfGeneratedPointValueCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C :
      PolynomialCertificateExtraction.GeneratedPointPositionValueCertificate
        F k hk) :
    GeneratedGlobalSeparationAt F k hk :=
  generatedGlobalSeparationOfPositionValueCertificate
    C.toPositionValueCertificate

theorem generatedGlobalSeparationOfGeneratedPointPolynomialFacts
    (F : RoleHingedPeriodSearchFamily)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
                  F hk i u j v)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  generatedGlobalSeparationOfGeneratedPointPolynomialCertificate
    ((PolynomialCertificateExtraction.polynomialCertificateFamilyOfGeneratedPointPolynomialFacts
      F polynomial_ge_one_lt).certificate k hk)

/-! ## Reduced metric hypothesis adapters -/

def reducedMetricHypothesesOfPositionPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C :
      NonConnectorPolynomialCertificates.PositionPolynomialCertificateFamily
        F) :
    ReducedMetricHypotheses (generatedChainFamilyOfRoleHinged F) :=
  ReducedMetricHypothesesProducerW20.ofCrossBlockLowerBounds
    C.toCrossBlockLowerBounds

def reducedMetricHypothesesOfPositionValueCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C :
      NonConnectorPolynomialCertificates.PositionValueCertificateFamily F) :
    ReducedMetricHypotheses (generatedChainFamilyOfRoleHinged F) :=
  reducedMetricHypothesesOfPositionPolynomialCertificateFamily
    C.toPositionPolynomialCertificateFamily

def reducedMetricHypothesesOfGeneratedPointPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily
        F) :
    ReducedMetricHypotheses (generatedChainFamilyOfRoleHinged F) :=
  reducedMetricHypothesesOfPositionPolynomialCertificateFamily
    (positionPolynomialCertificateFamilyOfGeneratedPoint C)

def reducedMetricHypothesesOfGeneratedPointValueCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily F) :
    ReducedMetricHypotheses (generatedChainFamilyOfRoleHinged F) :=
  reducedMetricHypothesesOfPositionValueCertificateFamily
    (positionValueCertificateFamilyOfGeneratedPoint C)

@[simp]
theorem reducedMetricHypothesesOfGeneratedPointPolynomialCertificateFamily_metric_separated
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily
        F)
    (k : Nat) (hk : 0 < k) :
    ((reducedMetricHypothesesOfGeneratedPointPolynomialCertificateFamily C).metric
        k hk).separated =
      C.separated k hk :=
  rfl

@[simp]
theorem reducedMetricHypothesesOfGeneratedPointValueCertificateFamily_metric_separated
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    ((reducedMetricHypothesesOfGeneratedPointValueCertificateFamily C).metric
        k hk).separated =
      C.toGeneratedPointPolynomialCertificateFamily.separated k hk :=
  rfl

def reducedMetricHypothesesOfGeneratedPointPolynomialFacts
    (F : RoleHingedPeriodSearchFamily)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
                  F hk i u j v) :
    ReducedMetricHypotheses (generatedChainFamilyOfRoleHinged F) :=
  reducedMetricHypothesesOfGeneratedPointPolynomialCertificateFamily
    (PolynomialCertificateExtraction.polynomialCertificateFamilyOfGeneratedPointPolynomialFacts
      F polynomial_ge_one_lt)

/-! ## Candidate and concrete package adapters -/

def reducedMetricHypothesesOfCandidatePolynomialCertificateFamily
    (C : NonConnectorPolynomialCertificates.CandidatePolynomialCertificateFamily) :
    ReducedMetricHypotheses
      (generatedChainFamilyOfRoleHinged C.toRoleHingedPeriodSearchFamily) :=
  reducedMetricHypothesesOfPositionPolynomialCertificateFamily
    C.certificates

def reducedMetricHypothesesOfCandidateValueCertificateFamily
    (C : NonConnectorPolynomialCertificates.CandidateValueCertificateFamily) :
    ReducedMetricHypotheses
      (generatedChainFamilyOfRoleHinged C.toRoleHingedPeriodSearchFamily) :=
  reducedMetricHypothesesOfCandidatePolynomialCertificateFamily
    C.toCandidatePolynomialCertificateFamily

def reducedMetricHypothesesOfCandidateGeneratedPointPolynomialCertificateFamily
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointPolynomialCertificateFamily) :
    ReducedMetricHypotheses
      (generatedChainFamilyOfRoleHinged C.toRoleHingedPeriodSearchFamily) :=
  reducedMetricHypothesesOfCandidatePolynomialCertificateFamily
    (candidatePolynomialCertificateFamilyOfGeneratedPoint C)

def reducedMetricHypothesesOfCandidateGeneratedPointValueCertificateFamily
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointValueCertificateFamily) :
    ReducedMetricHypotheses
      (generatedChainFamilyOfRoleHinged C.toRoleHingedPeriodSearchFamily) :=
  reducedMetricHypothesesOfCandidateValueCertificateFamily
    (candidateValueCertificateFamilyOfGeneratedPoint C)

def reducedMetricHypothesesOfConcreteGeneratedPointValueCertificateFamily
    (C :
      PolynomialCertificateExtraction.ConcreteGeneratedPointValueCertificateFamily) :
    ReducedMetricHypotheses
      (generatedChainFamilyOfRoleHinged C.toRoleHingedPeriodSearchFamily) :=
  ReducedMetricHypothesesProducerW20.ofConcreteValueMatrixFamily
    C.toConcreteValueMatrixFamily

theorem targetUpperConstructionFiveSixteen_ofGeneratedPointPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily
        F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (positionPolynomialCertificateFamilyOfGeneratedPoint C)
    |>.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_ofGeneratedPointPolynomialCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C :
      PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily
        F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (positionPolynomialCertificateFamilyOfGeneratedPoint C)
    |>.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_ofCandidateGeneratedPointPolynomialCertificateFamily
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointPolynomialCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (candidatePolynomialCertificateFamilyOfGeneratedPoint C)
    |>.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_ofCandidateGeneratedPointPolynomialCertificateFamily
    (C :
      PolynomialCertificateExtraction.CandidateGeneratedPointPolynomialCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (candidatePolynomialCertificateFamilyOfGeneratedPoint C)
    |>.targetUpperConstructionFiveSixteenArbitrary

end

end GeneratedPolynomialCertificateW21
end PachToth
end ErdosProblems1066
