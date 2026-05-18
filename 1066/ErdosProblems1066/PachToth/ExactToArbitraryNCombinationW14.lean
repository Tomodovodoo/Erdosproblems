import ErdosProblems1066.PachToth.ExactSixteenTargetW14
import ErdosProblems1066.PachToth.ArbitraryNEndpointW14
import ErdosProblems1066.PachToth.AllPositiveFiniteFieldsW14

set_option autoImplicit false

/-!
# W14 exact-to-arbitrary-n combination

This file combines the W14 exact `16 * k` certificate surfaces with the W14
arbitrary-`n` endpoint.  The route is only packaging:

* exact `16 * k` targets give W13 exact-chain certificates;
* W13 split soundness supplies the checked finite remainder construction for
  the `n / 16`, `n % 16` split;
* the arbitrary-`n` Pach--Toth target follows.

No unconditional closure is asserted here.  The finite certificate data remains
an explicit input through the imported W14/W13 certificate structures.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactToArbitraryNCombinationW14

noncomputable section

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev ExactBlockTarget (k : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt (16 * k)

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev ExactChainUpper (k : Nat) : Type :=
  SplitSoundness.ExactChainUpper k

abbrev ExistsCanonicalSplitRealization (k r : Nat) : Prop :=
  SplitSoundnessInstantiationW13.ExistsCanonicalSplitRealization k r

abbrev ExplicitAllPositiveCertificate :=
  ExactSixteenTargetW14.ExplicitAllPositiveCertificate

abbrev CandidatePolynomialCertificateFamily :=
  AllPositiveFiniteFieldsW14.CandidatePolynomialCertificateFamily

abbrev ExactMissingConcreteTableFields :=
  AllPositiveFiniteFieldsW14.ExactMissingConcreteTableFields

abbrev PeriodCandidateFamily :=
  AllPositiveFiniteFieldsW14.PeriodCandidateFamily

abbrev W12RawFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

abbrev W12TableFamilyPackage :=
  FiniteCertificateObligationsW12.TableFamilyPackage

abbrev W12VectorPackage :=
  FiniteCertificateObligationsW12.VectorPackage

abbrev W12ListPackage :=
  FiniteCertificateObligationsW12.ListPackage

/-! ## Exact block surfaces -/

/-- A surface of exact `16 * k` targets for every positive block count. -/
structure ExactBlockFamily where
  exactBlock : forall k : Nat, 0 < k -> ExactBlockTarget k

namespace ExactBlockFamily

/-- Exact block targets supply the exact-chain certificates expected by W13
split soundness. -/
def toExactChainFamily (C : ExactBlockFamily) :
    ArbitraryNEndpointW14.ExactChainFamily where
  exactChain := fun k hk =>
    SplitSoundnessInstantiationW13.exactChainUpperOfExactBlockTarget
      (C.exactBlock k hk)

def exactChainUpper
    (C : ExactBlockFamily) (k : Nat) (hk : 0 < k) :
    ExactChainUpper k :=
  C.toExactChainFamily.exactChain k hk

/-- The checked remainder route for the div/mod split of one arbitrary vertex
count. -/
theorem exists_canonicalSplitRealization_divMod
    (C : ExactBlockFamily) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  C.toExactChainFamily.exists_canonicalSplitRealization_divMod n

/-- Fixed arbitrary vertex count from exact `16 * k` targets plus checked
remainders. -/
theorem targetUpperConstructionFiveSixteenAt
    (C : ExactBlockFamily) (n : Nat) :
    FixedTarget n :=
  C.toExactChainFamily.targetUpperConstructionFiveSixteenAt n

/-- Arbitrary-`n` target from exact `16 * k` targets plus checked
remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (C : ExactBlockFamily) :
    ArbitraryTarget :=
  C.toExactChainFamily.targetUpperConstructionFiveSixteenArbitrary

end ExactBlockFamily

/-- Package an exact target surface into exact block targets. -/
def exactBlockFamilyOfExactTarget
    (H : PachToth.targetUpperConstructionFiveSixteen) :
    ExactBlockFamily where
  exactBlock := fun k hk => by
    rcases H k hk with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro s hs
    have hbound := hC s hs
    have hceil : Arithmetic.ceilDiv (5 * (16 * k)) 16 = 5 * k := by
      unfold Arithmetic.ceilDiv
      omega
    simpa [FixedTarget, ExactBlockTarget, targetUpperConstructionFiveSixteenAt,
      hceil] using hbound

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (H : PachToth.targetUpperConstructionFiveSixteen) :
    ArbitraryTarget :=
  (exactBlockFamilyOfExactTarget H).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt_of_exactBlocks
    (C : ExactBlockFamily) (n : Nat) :
    FixedTarget n :=
  C.targetUpperConstructionFiveSixteenAt n

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactBlocks
    (C : ExactBlockFamily) :
    ArbitraryTarget :=
  C.targetUpperConstructionFiveSixteenArbitrary

/-! ## Explicit exact-sixteen W14 finite certificate surfaces -/

/-- The W14 explicit all-positive finite certificate gives exact block targets
for every positive block count. -/
def exactBlockFamilyOfExplicitAllPositiveCertificate
    (C : ExplicitAllPositiveCertificate) :
    ExactBlockFamily where
  exactBlock := fun k hk =>
    ExactSixteenTargetW14.ExplicitAllPositiveCertificate.targetUpperConstructionFiveSixteenAt
      C k hk

theorem targetUpperConstructionFiveSixteenAt_of_explicitAllPositiveCertificate
    (C : ExplicitAllPositiveCertificate) (n : Nat) :
    FixedTarget n :=
  ExactBlockFamily.targetUpperConstructionFiveSixteenAt
    (exactBlockFamilyOfExplicitAllPositiveCertificate C) n

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitAllPositiveCertificate
    (C : ExplicitAllPositiveCertificate) :
    ArbitraryTarget :=
  ExactBlockFamily.targetUpperConstructionFiveSixteenArbitrary
    (exactBlockFamilyOfExplicitAllPositiveCertificate C)

theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_rawFields
    (C : W12RawFields) :
    ArbitraryTarget :=
  ArbitraryNEndpointW14.targetUpperConstructionFiveSixteenArbitrary_of_W12_rawFields
    C

theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_tableFamilyPackage
    (P : W12TableFamilyPackage) :
    ArbitraryTarget :=
  ArbitraryNEndpointW14.targetUpperConstructionFiveSixteenArbitrary_of_W12_tableFamilyPackage
    P

theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_vectorPackage
    (P : W12VectorPackage) :
    ArbitraryTarget :=
  ArbitraryNEndpointW14.targetUpperConstructionFiveSixteenArbitrary_of_W12_vectorPackage
    P

theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_listPackage
    (P : W12ListPackage) :
    ArbitraryTarget :=
  ArbitraryNEndpointW14.targetUpperConstructionFiveSixteenArbitrary_of_W12_listPackage
    P

/-! ## W14 all-positive polynomial finite fields -/

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_W12_rawFields
    (AllPositiveFiniteFieldsW14.fieldsOfCandidatePolynomialCertificateFamily C)

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactMissingConcreteTableFields
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_W12_rawFields D.toFields

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactMissingConcreteTablePackage
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_W12_tableFamilyPackage
    D.toTableFamilyPackage

/-! ## Named split-soundness bridge aliases -/

theorem exists_canonicalSplitRealization_of_exactChain_checkedRemainder
    {k r : Nat} (chain : ExactChainUpper k) :
    ExistsCanonicalSplitRealization k r :=
  SplitSoundnessInstantiationW13.exists_canonicalSplitRealization_of_exactChain_checkedRemainder
    chain

theorem targetUpperConstructionFiveSixteenAt_of_exactChain_checkedRemainder
    {k r : Nat} (hr : r < 16)
    (chain : ExactChainUpper k) :
    FixedTarget (16 * k + r) :=
  SplitSoundnessInstantiationW13.targetUpperConstructionFiveSixteenAt_of_exactChain_checkedRemainder
    hr chain

end

end ExactToArbitraryNCombinationW14
end PachToth
end ErdosProblems1066
