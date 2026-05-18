import ErdosProblems1066.PachToth.SplitSoundnessInstantiationW13
import ErdosProblems1066.PachToth.FiniteCertificateInstantiationW13
import ErdosProblems1066.PachToth.LargeClosedPlacementInstantiationW13

set_option autoImplicit false

/-!
# W14 arbitrary-n Pach-Toth endpoint

This endpoint keeps the final Pach-Toth arbitrary-n route conditional on
explicit data.  The checked route is:

* exact-chain data for the quotient block;
* the checked finite remainder construction;
* W13 split soundness for the div/mod vertex count.

Finite-certificate packages are routed by first extracting exact-chain
certificates for every positive block count.  Large closed-placement data is
kept threshold-aware: the remaining finite complement below the block
threshold is an explicit field.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNEndpointW14

noncomputable section

open SplitSoundnessInstantiationW13
open LargeClosedPlacementInstantiationW13

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ExactChainUpper (k : Nat) :=
  SplitSoundness.ExactChainUpper k

abbrev ExistsCanonicalSplitRealization (k r : Nat) : Prop :=
  SplitSoundnessInstantiationW13.ExistsCanonicalSplitRealization k r

abbrev W12RawFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

abbrev W12TableFamilyPackage :=
  FiniteCertificateObligationsW12.TableFamilyPackage

abbrev W12VectorPackage :=
  FiniteCertificateObligationsW12.VectorPackage

abbrev W12ListPackage :=
  FiniteCertificateObligationsW12.ListPackage

abbrev PeriodSearchDataFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :=
  FiniteCertificateObligationsW12.PeriodEquationFields.toRoleHingedPeriodSearchFamily
    (FiniteCertificateInstantiationW13.periodFieldsOfPeriodSearchData F)

abbrev PeriodCandidateFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily) :=
  FiniteCertificateObligationsW12.PeriodEquationFields.toRoleHingedPeriodSearchFamily
    (FiniteCertificateInstantiationW13.periodFieldsOfPeriodCandidateFamily F)

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeClosedPlacementInstantiationW13.LargeClosedPlacementFields K0

abbrev ExactBlockTarget (k : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt (16 * k)

/-! ## Exact-chain endpoint -/

/-- Exact-chain data for every positive quotient block.  The quotient-zero
case is supplied by `SplitSoundness.emptyExactChainUpper`. -/
structure ExactChainFamily where
  exactChain : forall k : Nat, 0 < k -> ExactChainUpper k

namespace ExactChainFamily

/-- Select the exact-chain certificate at the quotient `n / 16`, using the
empty exact chain when the quotient is zero. -/
def exactChainDiv (P : ExactChainFamily) (n : Nat) :
    ExactChainUpper (n / 16) := by
  by_cases hk : 0 < n / 16
  case pos =>
    exact P.exactChain (n / 16) hk
  case neg =>
    have hdiv : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
    rw [hdiv]
    exact SplitSoundness.emptyExactChainUpper

/-- Exact-chain data plus the checked remainder construction gives the W13
canonical split realization for the div/mod split of `n`. -/
theorem exists_canonicalSplitRealization_divMod
    (P : ExactChainFamily) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) := by
  exact
    exists_canonicalSplitRealization_of_exactChain_checkedRemainder
      (P.exactChainDiv n)

/-- Fixed vertex-count target from exact-chain quotient data, routed through
W13 split soundness. -/
theorem targetUpperConstructionFiveSixteenAt
    (P : ExactChainFamily) (n : Nat) :
    FixedTarget n := by
  exact
    targetUpperConstructionFiveSixteenAt_of_divMod_canonicalSplitRealization
      n
      (P.exists_canonicalSplitRealization_divMod n)

/-- Arbitrary vertex-count target from exact-chain data for all positive
quotient blocks. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (P : ExactChainFamily) :
    ArbitraryTarget := by
  intro n
  exact P.targetUpperConstructionFiveSixteenAt n

end ExactChainFamily

/-- A single quotient exact-chain certificate closes the fixed target at `n`
through W13 split soundness. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChainQuotient
    (n : Nat) (chain : ExactChainUpper (n / 16)) :
    FixedTarget n := by
  exact
    targetUpperConstructionFiveSixteenAt_of_divMod_canonicalSplitRealization
      n
      (exists_canonicalSplitRealization_of_exactChain_checkedRemainder
        (k := n / 16) (r := n % 16) chain)

/-- Exact-block target data gives exact-chain quotient data, then the W13
split endpoint gives arbitrary n. -/
def exactChainFamilyOfExactTarget (H : ExactTarget) :
    ExactChainFamily where
  exactChain := fun k _hk =>
    SplitSoundness.exactChainUpperOfTarget H k

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (H : ExactTarget) :
    ArbitraryTarget := by
  exact
    ExactChainFamily.targetUpperConstructionFiveSixteenArbitrary
      (exactChainFamilyOfExactTarget H)

/-! ## Finite-certificate endpoint -/

namespace FiniteCertificate

/-- W12 raw finite-certificate fields supply exact-chain data for every
positive block count. -/
def exactChainFamilyOfRawFields (C : W12RawFields) :
    ExactChainFamily where
  exactChain := fun k hk =>
    open FiniteCertificateObligationsW12.AllPositiveNonConnectorFields in
    SplitSoundnessInstantiationW13.exactChainUpperOfExactBlockTarget
      (targetUpperConstructionFiveSixteenAt_exactBlock C k hk)

/-- W12 native table packages supply exact-chain data for every positive
block count. -/
def exactChainFamilyOfTableFamilyPackage (P : W12TableFamilyPackage) :
    ExactChainFamily where
  exactChain := fun k hk =>
    open FiniteCertificateObligationsW12.TableFamilyPackage in
    SplitSoundnessInstantiationW13.exactChainUpperOfExactBlockTarget
      (targetUpperConstructionFiveSixteenAt_exactBlock P k hk)

/-- W12 vector packages supply exact-chain data for every positive block
count. -/
def exactChainFamilyOfVectorPackage (P : W12VectorPackage) :
    ExactChainFamily where
  exactChain := fun k hk =>
    open FiniteCertificateObligationsW12.VectorPackage in
    SplitSoundnessInstantiationW13.exactChainUpperOfExactBlockTarget
      (targetUpperConstructionFiveSixteenAt_exactBlock P k hk)

/-- W12 list packages supply exact-chain data for every positive block
count. -/
def exactChainFamilyOfListPackage (P : W12ListPackage) :
    ExactChainFamily where
  exactChain := fun k hk =>
    open FiniteCertificateObligationsW12.ListPackage in
    SplitSoundnessInstantiationW13.exactChainUpperOfExactBlockTarget
      (targetUpperConstructionFiveSixteenAt_exactBlock P k hk)

theorem targetUpperConstructionFiveSixteenAt_of_rawFields
    (C : W12RawFields) (n : Nat) :
    FixedTarget n :=
  ExactChainFamily.targetUpperConstructionFiveSixteenAt
    (exactChainFamilyOfRawFields C) n

theorem targetUpperConstructionFiveSixteenArbitrary_of_rawFields
    (C : W12RawFields) :
    ArbitraryTarget :=
  ExactChainFamily.targetUpperConstructionFiveSixteenArbitrary
    (exactChainFamilyOfRawFields C)

theorem targetUpperConstructionFiveSixteenArbitrary_of_tableFamilyPackage
    (P : W12TableFamilyPackage) :
    ArbitraryTarget :=
  ExactChainFamily.targetUpperConstructionFiveSixteenArbitrary
    (exactChainFamilyOfTableFamilyPackage P)

theorem targetUpperConstructionFiveSixteenArbitrary_of_vectorPackage
    (P : W12VectorPackage) :
    ArbitraryTarget :=
  ExactChainFamily.targetUpperConstructionFiveSixteenArbitrary
    (exactChainFamilyOfVectorPackage P)

theorem targetUpperConstructionFiveSixteenArbitrary_of_listPackage
    (P : W12ListPackage) :
    ArbitraryTarget :=
  ExactChainFamily.targetUpperConstructionFiveSixteenArbitrary
    (exactChainFamilyOfListPackage P)

def exactChainFamilyOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    ExactChainFamily :=
  exactChainFamilyOfRawFields
    (FiniteCertificateInstantiationW13.fieldsOfConcreteValueMatrixFamily C)

def exactChainFamilyOfCandidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    ExactChainFamily :=
  exactChainFamilyOfRawFields
    (FiniteCertificateInstantiationW13.fieldsOfCandidateValueMatrixFamily C)

theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    ArbitraryTarget :=
  ExactChainFamily.targetUpperConstructionFiveSixteenArbitrary
    (exactChainFamilyOfConcreteValueMatrixFamily C)

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    ArbitraryTarget :=
  ExactChainFamily.targetUpperConstructionFiveSixteenArbitrary
    (exactChainFamilyOfCandidateValueMatrixFamily C)

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_tableFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      FiniteCertificateObligationsW12.UpperTriangleNonConnectorSqValueTableFamily
        (PeriodSearchDataFamily F)) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_tableFamilyPackage
    (FiniteCertificateInstantiationW13.tableFamilyPackageOfPeriodSearchData F T)

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_vectorFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      FiniteCertificateObligationsW12.VectorTableFamily
        (PeriodSearchDataFamily F)) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_vectorPackage
    (FiniteCertificateInstantiationW13.vectorPackageOfPeriodSearchData F T)

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_listFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      FiniteCertificateObligationsW12.ListTableFamily
        (PeriodSearchDataFamily F)) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_listPackage
    (FiniteCertificateInstantiationW13.listPackageOfPeriodSearchData F T)

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodCandidateFamily_tableFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      FiniteCertificateObligationsW12.UpperTriangleNonConnectorSqValueTableFamily
        (PeriodCandidateFamily F)) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_tableFamilyPackage
    (FiniteCertificateInstantiationW13.tableFamilyPackageOfPeriodCandidateFamily F T)

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodCandidateFamily_vectorFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      FiniteCertificateObligationsW12.VectorTableFamily
        (PeriodCandidateFamily F)) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_vectorPackage
    (FiniteCertificateInstantiationW13.vectorPackageOfPeriodCandidateFamily F T)

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodCandidateFamily_listFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      FiniteCertificateObligationsW12.ListTableFamily
        (PeriodCandidateFamily F)) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_listPackage
    (FiniteCertificateInstantiationW13.listPackageOfPeriodCandidateFamily F T)

end FiniteCertificate

/-! ## Large closed-placement endpoint -/

namespace LargeClosedPlacement

/-- Large closed-placement data gives the W13 split target in the certified
large block range. -/
theorem targetUpperConstructionFiveSixteenAt_of_largeClosedPlacementFields
    {K0 k r : Nat} (L : LargeClosedPlacementFields K0)
    (hK : K0 <= k) (hk : 0 < k) (hr : r < 16) :
    FixedTarget (16 * k + r) :=
  targetUpperConstructionFiveSixteenAt_of_W12_largeClosedPlacement
    L hK hk hr

/-- Source-faithful eventual target from large closed-placement fields. -/
theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    EventualTarget :=
  targetUpperConstructionFiveSixteenEventually_of_largeClosedPlacementFields
    L

/-- The exact remaining data for a large closed-placement route: exact-chain
certificates for each positive block count below the large threshold. -/
structure WithSmallExactChains (K0 : Nat) where
  large : LargeClosedPlacementFields K0
  smallExactChains :
    forall k : Nat, k < K0 -> 0 < k -> ExactChainUpper k

namespace WithSmallExactChains

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : WithSmallExactChains K0) :
    EventualTarget :=
  LargeClosedPlacement.targetUpperConstructionFiveSixteenEventually P.large

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : WithSmallExactChains K0) :
    ArbitraryTarget :=
  arbitraryTarget_of_largeClosedPlacementFields_blockSmallChains
    P.large P.smallExactChains

end WithSmallExactChains

/-- Equivalent finite complement form: exact-block targets for each positive
block count below the large threshold. -/
structure WithSmallExactBlocks (K0 : Nat) where
  large : LargeClosedPlacementFields K0
  smallExactBlocks :
    forall k : Nat, k < K0 -> 0 < k -> ExactBlockTarget k

namespace WithSmallExactBlocks

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : WithSmallExactBlocks K0) :
    EventualTarget :=
  LargeClosedPlacement.targetUpperConstructionFiveSixteenEventually P.large

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : WithSmallExactBlocks K0) :
    ArbitraryTarget :=
  arbitraryTarget_of_largeClosedPlacementFields_exactBlockSmallTargets
    P.large P.smallExactBlocks

end WithSmallExactBlocks

/-- All-positive finite fields close the finite complement below any large
closed-placement threshold. -/
structure WithAllPositiveFiniteFields (K0 : Nat) where
  large : LargeClosedPlacementFields K0
  finite : W12RawFields

namespace WithAllPositiveFiniteFields

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : WithAllPositiveFiniteFields K0) :
    EventualTarget :=
  LargeClosedPlacement.targetUpperConstructionFiveSixteenEventually P.large

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : WithAllPositiveFiniteFields K0) :
    ArbitraryTarget :=
  arbitraryTarget_of_largeClosedPlacementFields_allPositiveFiniteFields
    P.large P.finite

end WithAllPositiveFiniteFields

end LargeClosedPlacement

/-! ## Endpoint aliases -/

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactChains
    (P : ExactChainFamily) :
    ArbitraryTarget :=
  ExactChainFamily.targetUpperConstructionFiveSixteenArbitrary P

theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_rawFields
    (C : W12RawFields) :
    ArbitraryTarget :=
  FiniteCertificate.targetUpperConstructionFiveSixteenArbitrary_of_rawFields C

theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_tableFamilyPackage
    (P : W12TableFamilyPackage) :
    ArbitraryTarget :=
  FiniteCertificate.targetUpperConstructionFiveSixteenArbitrary_of_tableFamilyPackage
    P

theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_vectorPackage
    (P : W12VectorPackage) :
    ArbitraryTarget :=
  FiniteCertificate.targetUpperConstructionFiveSixteenArbitrary_of_vectorPackage P

theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_listPackage
    (P : W12ListPackage) :
    ArbitraryTarget :=
  FiniteCertificate.targetUpperConstructionFiveSixteenArbitrary_of_listPackage P

theorem targetUpperConstructionFiveSixteenArbitrary_of_largeClosedPlacement_smallExactChains
    {K0 : Nat} (P : LargeClosedPlacement.WithSmallExactChains K0) :
    ArbitraryTarget :=
  LargeClosedPlacement.WithSmallExactChains.targetUpperConstructionFiveSixteenArbitrary
    P

theorem targetUpperConstructionFiveSixteenArbitrary_of_largeClosedPlacement_smallExactBlocks
    {K0 : Nat} (P : LargeClosedPlacement.WithSmallExactBlocks K0) :
    ArbitraryTarget :=
  LargeClosedPlacement.WithSmallExactBlocks.targetUpperConstructionFiveSixteenArbitrary
    P

theorem targetUpperConstructionFiveSixteenArbitrary_of_largeClosedPlacement_allPositiveFiniteFields
    {K0 : Nat} (P : LargeClosedPlacement.WithAllPositiveFiniteFields K0) :
    ArbitraryTarget :=
  LargeClosedPlacement.WithAllPositiveFiniteFields.targetUpperConstructionFiveSixteenArbitrary
    P

end

end ArbitraryNEndpointW14
end PachToth
end ErdosProblems1066
