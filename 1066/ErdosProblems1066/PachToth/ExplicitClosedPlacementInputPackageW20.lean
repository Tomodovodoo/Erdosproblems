import ErdosProblems1066.PachToth.ExplicitClosedPlacementProducerW19

set_option autoImplicit false

/-!
# W20 explicit closed-placement input package

This file is the W20 handoff into
`ExplicitClosedPlacementProducerW19.InputPackage`.  The assumptions are kept at
the reduced generated-family level: a generated chain family, algebraic
closure equations for every positive block count, and reduced metric
hypotheses for that same family.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExplicitClosedPlacementInputPackageW20

noncomputable section

abbrev W19InputPackage : Type :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev GeneratedChainFamily : Type :=
  ExplicitClosedPlacementProducerW19.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementProducerW19.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementProducerW19.ReducedMetricHypotheses F

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  ExplicitClosedPlacementProducerW19.ExplicitClosedPlacementCertificateFamily

abbrev ExactTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ExactTarget

abbrev ArbitraryTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ArbitraryTarget

abbrev FixedTarget (n : Nat) : Prop :=
  ExplicitClosedPlacementProducerW19.FixedTarget n

abbrev ExactBlockTarget (k : Nat) : Prop :=
  ExplicitClosedPlacementProducerW19.ExactBlockTarget k

/-- W20 source fields: the weakest reduced generated-family assumptions needed
by the W19 explicit closed-placement producer. -/
structure GeneratedFamilyClosureReducedMetricSourceFields where
  family : GeneratedChainFamily
  closure : GeneratedChainFamilyClosures family
  reducedMetric : ReducedMetricHypotheses family

namespace GeneratedFamilyClosureReducedMetricSourceFields

/-- Assemble the W19 input package from the W20 source fields. -/
def toInputPackage
    (S : GeneratedFamilyClosureReducedMetricSourceFields) :
    W19InputPackage where
  family := S.family
  closure := S.closure
  metric := S.reducedMetric

@[simp]
theorem toInputPackage_family
    (S : GeneratedFamilyClosureReducedMetricSourceFields) :
    S.toInputPackage.family = S.family :=
  rfl

@[simp]
theorem toInputPackage_closure
    (S : GeneratedFamilyClosureReducedMetricSourceFields) :
    S.toInputPackage.closure = S.closure :=
  rfl

@[simp]
theorem toInputPackage_metric
    (S : GeneratedFamilyClosureReducedMetricSourceFields) :
    S.toInputPackage.metric = S.reducedMetric :=
  rfl

/-- The explicit closed-placement certificate family produced from the W20
source fields. -/
def explicitClosedPlacementCertificateFamily
    (S : GeneratedFamilyClosureReducedMetricSourceFields) :
    ExplicitClosedPlacementCertificateFamily :=
  S.toInputPackage.explicitClosedPlacementCertificate

/-- Exact-block target from the W20 source fields. -/
theorem targetUpperConstructionFiveSixteen
    (S : GeneratedFamilyClosureReducedMetricSourceFields) :
    ExactTarget :=
  S.toInputPackage.targetUpperConstructionFiveSixteen

/-- Exact target at a concrete block count from the W20 source fields. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (S : GeneratedFamilyClosureReducedMetricSourceFields)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  S.toInputPackage.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Arbitrary-vertex target from the W20 source fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (S : GeneratedFamilyClosureReducedMetricSourceFields) :
    ArbitraryTarget :=
  S.toInputPackage.targetUpperConstructionFiveSixteenArbitrary

/-- Pointwise arbitrary target from the W20 source fields. -/
theorem targetUpperConstructionFiveSixteenAt
    (S : GeneratedFamilyClosureReducedMetricSourceFields) (n : Nat) :
    FixedTarget n :=
  S.toInputPackage.targetUpperConstructionFiveSixteenAt n

end GeneratedFamilyClosureReducedMetricSourceFields

/-- Assemble the W19 input package from exactly a generated family, its
closure equations, and its reduced metric hypotheses. -/
def inputPackage_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F) :
    W19InputPackage where
  family := F
  closure := closure
  metric := reducedMetric

/-- The source-field bundle corresponding to the weakest raw assumptions. -/
def sourceFields_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F) :
    GeneratedFamilyClosureReducedMetricSourceFields where
  family := F
  closure := closure
  reducedMetric := reducedMetric

/-- The requested explicit closed-placement certificate family from exactly a
generated family, its closure equations, and reduced metric hypotheses. -/
def explicitClosedPlacementCertificateFamily_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F) :
    ExplicitClosedPlacementCertificateFamily :=
  (inputPackage_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric).explicitClosedPlacementCertificate

/-- Exact-block target from exactly a generated family, its closure equations,
and reduced metric hypotheses. -/
theorem targetUpperConstructionFiveSixteen_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F) :
    ExactTarget :=
  (inputPackage_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric).targetUpperConstructionFiveSixteen

/-- Exact target at `16 * k` from exactly a generated family, its closure
equations, and reduced metric hypotheses. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  (inputPackage_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric).targetUpperConstructionFiveSixteenAt_exactBlock
      k hk

/-- Arbitrary-vertex target from exactly a generated family, its closure
equations, and reduced metric hypotheses. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F) :
    ArbitraryTarget :=
  (inputPackage_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric).targetUpperConstructionFiveSixteenArbitrary

/-- Pointwise arbitrary target from exactly a generated family, its closure
equations, and reduced metric hypotheses. -/
theorem targetUpperConstructionFiveSixteenAt_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F)
    (n : Nat) :
    FixedTarget n :=
  (targetUpperConstructionFiveSixteenArbitrary_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric) n

/-- Public upper-bound wrapper for arbitrary vertex count `n`, under exactly
the reduced generated-family assumptions. -/
theorem upper_bound_five_sixteen_arbitrary_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenAt_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric n

end

end ExplicitClosedPlacementInputPackageW20

theorem targetUpperConstructionFiveSixteen_of_w20_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : ExplicitClosedPlacementInputPackageW20.GeneratedChainFamily)
    (closure :
      ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures F)
    (reducedMetric :
      ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses F) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen :=
  ExplicitClosedPlacementInputPackageW20.targetUpperConstructionFiveSixteen_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric

theorem targetUpperConstructionFiveSixteenArbitrary_of_w20_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : ExplicitClosedPlacementInputPackageW20.GeneratedChainFamily)
    (closure :
      ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures F)
    (reducedMetric :
      ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses F) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ExplicitClosedPlacementInputPackageW20.targetUpperConstructionFiveSixteenArbitrary_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric

theorem upper_bound_five_sixteen_arbitrary_of_w20_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : ExplicitClosedPlacementInputPackageW20.GeneratedChainFamily)
    (closure :
      ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures F)
    (reducedMetric :
      ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses F)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  ExplicitClosedPlacementInputPackageW20.upper_bound_five_sixteen_arbitrary_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric n

end PachToth

namespace Verified

abbrev PachTothW20GeneratedFamilyClosureReducedMetricSourceFields :=
  PachToth.ExplicitClosedPlacementInputPackageW20.GeneratedFamilyClosureReducedMetricSourceFields

abbrev PachTothW20ExplicitClosedPlacementCertificateFamily :=
  PachToth.ExplicitClosedPlacementInputPackageW20.ExplicitClosedPlacementCertificateFamily

/-- Public W20 certificate-family producer under the exact reduced
generated-family assumptions. -/
def pachtothW20ExplicitClosedPlacementCertificateFamily_of_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : PachToth.ExplicitClosedPlacementInputPackageW20.GeneratedChainFamily)
    (closure :
      PachToth.ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures
        F)
    (reducedMetric :
      PachToth.ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses
        F) :
    PachTothW20ExplicitClosedPlacementCertificateFamily :=
  PachToth.ExplicitClosedPlacementInputPackageW20.explicitClosedPlacementCertificateFamily_of_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric

theorem targetUpperConstructionFiveSixteen_of_pachtoth_w20_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : PachToth.ExplicitClosedPlacementInputPackageW20.GeneratedChainFamily)
    (closure :
      PachToth.ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures
        F)
    (reducedMetric :
      PachToth.ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses
        F) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen :=
  PachToth.targetUpperConstructionFiveSixteen_of_w20_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric

theorem targetUpperConstructionFiveSixteenArbitrary_of_pachtoth_w20_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : PachToth.ExplicitClosedPlacementInputPackageW20.GeneratedChainFamily)
    (closure :
      PachToth.ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures
        F)
    (reducedMetric :
      PachToth.ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses
        F) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary_of_w20_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w20_generatedChainFamilyClosures_reducedMetricHypotheses
    (F : PachToth.ExplicitClosedPlacementInputPackageW20.GeneratedChainFamily)
    (closure :
      PachToth.ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures
        F)
    (reducedMetric :
      PachToth.ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses
        F)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w20_generatedChainFamilyClosures_reducedMetricHypotheses
    F closure reducedMetric n

end Verified
end ErdosProblems1066
