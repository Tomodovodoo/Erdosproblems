import ErdosProblems1066.PachToth.ExactFamilyClosure
import ErdosProblems1066.PachToth.NonRigidClosedPlacementDataW19
import ErdosProblems1066.PachToth.ClosedPlacementTargetWrappersW19
import ErdosProblems1066.PachToth.ArbitraryNClosedPlacementRouteW19
import ErdosProblems1066.PachToth.ClosedPlacementObstructionBypassW19

set_option autoImplicit false

/-!
# W19 explicit closed-placement producer

This file is the W19 handoff for the requested certificate family

`forall k hk, ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk`.

The current workspace does not contain an unconditional non-rigid closed-chain
producer: the W18 base-fixing route is explicitly blocked by
`ClosedPlacementObstructionBypassW19`.  Consequently, the endpoint below is
conditional on the minimal generated-chain input package already used by the
closed-placement closure route: a generated family, algebraic closure for each
positive block count, and reduced metric hypotheses for that same family.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExplicitClosedPlacementProducerW19

open ArbitraryNClosedPlacementRouteW19
open ClosedPlacementObstructionBypassW19
open ClosedPlacementTargetWrappersW19
open NonRigidClosedPlacementDataW19

noncomputable section

abbrev ExplicitClosedPlacementCertificate
    (k : Nat) (hk : 0 < k) :=
  ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    ExplicitClosedPlacementCertificate k hk

abbrev GeneratedChainFamily :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) :=
  ClosedPlacementClosure.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) :=
  GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F

abbrev GeneratedReducedObligations
    (F : GeneratedChainFamily) :=
  NonRigidClosedPlacementDataW19.GeneratedReducedClosedPlacementFamilyObligations F

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

abbrev ExactBlockTarget (k : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt (16 * k)

/-- The minimal input package needed to produce explicit closed-placement
certificates for every positive block count. -/
structure InputPackage where
  family : GeneratedChainFamily
  closure : GeneratedChainFamilyClosures family
  metric : ReducedMetricHypotheses family

namespace InputPackage

/-- Repackage the W19 input package as the existing exact-family facade. -/
def toExactFamilyHypotheses
    (P : InputPackage) :
    ExactFamilyClosure.ExactFamilyHypotheses where
  family := P.family
  closure := P.closure
  metric := P.metric

/-- Repackage closure equations as generated-period obligations for the
compiled non-rigid W19 data facade. -/
def toGeneratedReducedClosedPlacementFamilyObligations
    (P : InputPackage) :
    GeneratedReducedObligations P.family where
  periods :=
    ClosedPlacementClosure.generatedChainFamilyPeriodsOfClosures
      P.family P.closure
  reducedMetric := P.metric

/-- The requested explicit closed-placement certificate family, produced from
the generated closure and reduced metric data. -/
def explicitClosedPlacementCertificate
    (P : InputPackage) :
    ExplicitClosedPlacementCertificateFamily :=
  GeneratedReducedClosedPlacementFamilyObligations.toCertificateFamily
    P.toGeneratedReducedClosedPlacementFamilyObligations

/-- The same certificate family routed through the older exact-family facade. -/
def explicitClosedPlacementCertificate_exactFamilyRoute
    (P : InputPackage) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk =>
    P.toExactFamilyHypotheses.explicitClosedPlacementCertificate k hk

/-- The checked closed-placement family carried by the explicit certificates. -/
def closedPlacementFamily
    (P : InputPackage) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk => (P.explicitClosedPlacementCertificate k hk).toClosedPlacement

/-- The compiled W19 target-wrapper producer surface for this package. -/
def certificateProducer
    (P : InputPackage) :
    ClosedPlacementCertificateProducer where
  certificate := P.explicitClosedPlacementCertificate

@[simp]
theorem certificateProducer_certificate
    (P : InputPackage) :
    P.certificateProducer.certificate =
      P.explicitClosedPlacementCertificate :=
  rfl

/-- Exact-block target at `16 * k` from the produced certificate at `k`. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (P : InputPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificates
        P.explicitClosedPlacementCertificate k hk

/-- Exact `16 * k` Pach--Toth target from the produced certificate family. -/
theorem targetUpperConstructionFiveSixteen
    (P : InputPackage) :
    ExactTarget := by
  exact
    targetUpperConstructionFiveSixteen_of_certificateProducer
        P.certificateProducer

/-- The same exact target, routed directly through the exact-family facade. -/
theorem targetUpperConstructionFiveSixteen_exactFamilyRoute
    (P : InputPackage) :
    ExactTarget := by
  exact
    ExactFamilyClosure.targetUpperConstructionFiveSixteen_of_exactFamilyHypotheses
      P.toExactFamilyHypotheses

/-- The exact target routed through the non-rigid W19 certificate-family
wrapper. -/
theorem targetUpperConstructionFiveSixteen_nonRigidRoute
    (P : InputPackage) :
    ExactTarget := by
  exact
    targetUpperConstructionFiveSixteen_of_certificateFamily
      P.explicitClosedPlacementCertificate

/-- Arbitrary-`n` Pach--Toth target from the produced explicit certificates. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (P : InputPackage) :
    ArbitraryTarget := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
        P.explicitClosedPlacementCertificate

/-- The arbitrary-`n` target routed through the non-rigid W19
certificate-family wrapper. -/
theorem targetUpperConstructionFiveSixteenArbitrary_nonRigidRoute
    (P : InputPackage) :
    ArbitraryTarget := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_certificateFamily
      P.explicitClosedPlacementCertificate

/-- The pointwise arbitrary target extracted from the arbitrary-`n` theorem. -/
theorem targetUpperConstructionFiveSixteenAt
    (P : InputPackage) (n : Nat) :
    FixedTarget n :=
  P.targetUpperConstructionFiveSixteenArbitrary n

/-- Public upper-bound wrapper for arbitrary vertex count `n`. -/
theorem upper_bound_five_sixteen_arbitrary
    (P : InputPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  P.targetUpperConstructionFiveSixteenAt n

end InputPackage

/-- Public producer name: from the minimal W19 input package, produce the
requested explicit closed-placement certificate family. -/
def explicitClosedPlacementCertificate
    (P : InputPackage) :
    ExplicitClosedPlacementCertificateFamily :=
  P.explicitClosedPlacementCertificate

/-- Exact target reduction from the minimal W19 input package. -/
theorem targetUpperConstructionFiveSixteen_of_inputPackage
    (P : InputPackage) :
    ExactTarget :=
  P.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target reduction from the minimal W19 input package. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    (P : InputPackage) :
    ArbitraryTarget :=
  P.targetUpperConstructionFiveSixteenArbitrary

/-- The W18 all-positive input route is blocked in this workspace by the
base-fixing obstruction recorded in the compiled W19 bypass helper. -/
theorem not_nonempty_w18_allPositiveFinalCertificateInputs :
    Not
      (Nonempty
        AllPositiveFinalCertificateInputs) :=
  not_nonempty_allPositiveFinalCertificateInputs

/-- The value-input variant of the W18 all-positive route is likewise blocked. -/
theorem not_nonempty_w18_allPositiveFinalCertificateValueInputs :
    Not
      (Nonempty
        AllPositiveFinalCertificateValueInputs) :=
  not_nonempty_allPositiveFinalCertificateValueInputs

end

end ExplicitClosedPlacementProducerW19
end PachToth
end ErdosProblems1066
