import ErdosProblems1066.PachToth.ArbitraryNNonRoleSourceW24
import ErdosProblems1066.PachToth.ArbitraryNBridgeW10
import ErdosProblems1066.PachToth.ConcreteRemainderSplitW24
import ErdosProblems1066.PachToth.FullMetricClosedPlacementW24
import ErdosProblems1066.PachToth.FreePlacementSourceFieldsW24
import ErdosProblems1066.PachToth.AlternativeValueMatrixFamilyW24
import ErdosProblems1066.PachToth.SmallLengthExactTargetsConcreteW24

set_option autoImplicit false

/-!
# W25 non-role split-source inhabitance bridges

This file attacks the actual inhabitance surface of
`ArbitraryNNonRoleSourceW24.NonRoleSplitSource`.  The source needs exactly
positive exact-chain upper certificates, so the live result is an exact
equivalence with the older W10 positive exact-chain package and with the
exact `16 * k` target.  Closed-placement, full-metric, free-placement, and
alternative value-matrix W24 packages are then routed into that same minimal
source without adding any unchecked assumptions.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonRoleSplitSourceInhabitationW25

open Arithmetic

noncomputable section

abbrev NonRoleSplitSource : Type :=
  ArbitraryNNonRoleSourceW24.NonRoleSplitSource

abbrev PositiveExactChainPackage : Type :=
  ArbitraryNBridgeW10.PositiveExactChainPackage

abbrev ExactChainUpper (k : Nat) : Type :=
  SplitSoundness.ExactChainUpper k

abbrev ExactBlockTarget (k : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt (16 * k)

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev FullMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness

abbrev ReducedMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementSourceFieldsW24.MinimalFreePlacementFields

abbrev AlternativeValueMatrixFamily : Type :=
  AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily

/-! ## The exact-chain source is the same source -/

/-- The W24 non-role source repackaged as the smallest older exact-chain
package. -/
def positiveExactChainPackageOfNonRoleSplitSource
    (S : NonRoleSplitSource) :
    PositiveExactChainPackage where
  exactChain := S.exactChain

/-- The W10 positive exact-chain package repackaged as the W24 non-role
source. -/
def nonRoleSplitSourceOfPositiveExactChainPackage
    (P : PositiveExactChainPackage) :
    NonRoleSplitSource where
  exactChain := P.exactChain

theorem nonRoleSplitSource_positiveExactChainPackage_left_inverse
    (S : NonRoleSplitSource) :
    nonRoleSplitSourceOfPositiveExactChainPackage
      (positiveExactChainPackageOfNonRoleSplitSource S) = S := by
  cases S
  rfl

theorem nonRoleSplitSource_positiveExactChainPackage_right_inverse
    (P : PositiveExactChainPackage) :
    positiveExactChainPackageOfNonRoleSplitSource
      (nonRoleSplitSourceOfPositiveExactChainPackage P) = P := by
  cases P
  rfl

/-- Inhabiting the W24 non-role source is exactly inhabiting the smallest
known positive exact-chain package. -/
theorem nonempty_nonRoleSplitSource_iff_positiveExactChainPackage :
    Nonempty NonRoleSplitSource <-> Nonempty PositiveExactChainPackage := by
  constructor
  · intro h
    rcases h with ⟨S⟩
    exact Nonempty.intro (positiveExactChainPackageOfNonRoleSplitSource S)
  · intro h
    rcases h with ⟨P⟩
    exact Nonempty.intro (nonRoleSplitSourceOfPositiveExactChainPackage P)

/-! ## Exact target and exact-block target equivalences -/

theorem exactTarget_of_nonRoleSplitSource
    (S : NonRoleSplitSource) :
    ExactTarget :=
  S.exactTarget

def nonRoleSplitSourceOfExactTarget
    (H : ExactTarget) :
    NonRoleSplitSource :=
  ArbitraryNNonRoleSourceW24.NonRoleSplitSource.ofExactTarget H

/-- The source is inhabited exactly when the full exact chain target is
available.  This is the tight Prop-level inhabitance statement: no source is
constructed unless the exact `16 * k` target is already live. -/
theorem nonempty_nonRoleSplitSource_iff_exactTarget :
    Nonempty NonRoleSplitSource <-> ExactTarget := by
  constructor
  · intro h
    rcases h with ⟨S⟩
    exact exactTarget_of_nonRoleSplitSource S
  · intro H
    exact Nonempty.intro (nonRoleSplitSourceOfExactTarget H)

/-- Exact-block targets for every positive `k` are another spelling of the
same source, with the exact-chain constructors supplied by the exact-block
target module. -/
def nonRoleSplitSourceOfExactBlockTargets
    (H : forall k : Nat, 0 < k -> ExactBlockTarget k) :
    NonRoleSplitSource where
  exactChain := fun k hk =>
    SmallLengthExactTargetsConcreteW24.exactChainUpperOfExactBlockTarget
      (H k hk)

theorem nonempty_nonRoleSplitSource_iff_exactBlockTargets :
    Nonempty NonRoleSplitSource <->
      (forall k : Nat, 0 < k -> ExactBlockTarget k) := by
  constructor
  · intro h k hk
    rcases h with ⟨S⟩
    exact
      SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_exactChainUpper
        (S.exactChain k hk)
  · intro H
    exact Nonempty.intro (nonRoleSplitSourceOfExactBlockTargets H)

/-! ## Split-certificate and translated-remainder route -/

/-- A non-role source gives canonical split realizations after translating the
checked remainder far away.  This names the `SplitCertificateBridge` endpoint
used by the arbitrary-`n` soundness theorem. -/
def canonicalSplitRealizationOfNonRoleSplitSource
    (S : NonRoleSplitSource) (k r : Nat) :
    SplitSoundness.CanonicalSplitRealization k r :=
  RemainderPlacement.canonicalSplitRealizationOfExactChainTranslatedRemainder
    (S.exactChainAt k)
    (SplitSoundness.remainderUpperOfConstruction r)

theorem exists_canonicalSplitRealization_of_nonRoleSplitSource
    (S : NonRoleSplitSource) (k r : Nat) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r := by
  exact ⟨canonicalSplitRealizationOfNonRoleSplitSource S k r, True.intro⟩

theorem targetUpperConstructionFiveSixteenAt_of_nonRoleSplitSource_splitBridge
    (S : NonRoleSplitSource) {k r : Nat} (hr : r < 16) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr
      (exists_canonicalSplitRealization_of_nonRoleSplitSource S k r)

theorem targetUpperConstructionFiveSixteenAt_divMod_of_nonRoleSplitSource
    (S : NonRoleSplitSource) (n : Nat) :
    targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      (Nat.mod_lt n (by norm_num))
      (S.exactChainAt (n / 16))
      (SplitSoundness.remainderUpperOfConstruction (n % 16))

theorem arbitraryTarget_of_nonRoleSplitSource
    (S : NonRoleSplitSource) :
    ArbitraryTarget :=
  S.arbitraryTarget

/-! ## Constructors from live closed-placement data -/

/-- Direct live closed-placement data constructs the non-role source by
forgetting each closed placement to its exact-chain upper certificate. -/
def nonRoleSplitSourceOfClosedPlacements
    (H : forall k : Nat, forall hk : 0 < k,
      DeformedPlacement.ClosedPlacement k hk) :
    NonRoleSplitSource where
  exactChain := fun k hk =>
    SplitCertificateBridge.exactChainUpperOfClosedPlacement (H k hk)

theorem exactTarget_of_closedPlacements
    (H : forall k : Nat, forall hk : 0 < k,
      DeformedPlacement.ClosedPlacement k hk) :
    ExactTarget :=
  (nonRoleSplitSourceOfClosedPlacements H).exactTarget

def nonRoleSplitSourceOfFullMetricClosedPlacementWitness
    (W : FullMetricClosedPlacementWitness) :
    NonRoleSplitSource :=
  nonRoleSplitSourceOfClosedPlacements W.closedPlacement

theorem exactTarget_of_fullMetricClosedPlacementWitness
    (W : FullMetricClosedPlacementWitness) :
    ExactTarget :=
  (nonRoleSplitSourceOfFullMetricClosedPlacementWitness W).exactTarget

def nonRoleSplitSourceOfReducedMetricClosedPlacementWitness
    (W : ReducedMetricClosedPlacementWitness) :
    NonRoleSplitSource :=
  nonRoleSplitSourceOfClosedPlacements W.closedPlacement

theorem exactTarget_of_reducedMetricClosedPlacementWitness
    (W : ReducedMetricClosedPlacementWitness) :
    ExactTarget :=
  (nonRoleSplitSourceOfReducedMetricClosedPlacementWitness W).exactTarget

def nonRoleSplitSourceOfFreePlacementSourceFields
    (S : MinimalFreePlacementFields) :
    NonRoleSplitSource :=
  nonRoleSplitSourceOfClosedPlacements S.toClosedPlacement

theorem exactTarget_of_freePlacementSourceFields
    (S : MinimalFreePlacementFields) :
    ExactTarget :=
  (nonRoleSplitSourceOfFreePlacementSourceFields S).exactTarget

/-- The alternative W24 value-matrix package reaches the non-role source
through its checked exact-target bridge. -/
def nonRoleSplitSourceOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    NonRoleSplitSource :=
  nonRoleSplitSourceOfExactTarget
    (AlternativeValueMatrixFamilyW24.exactTarget_of_alternativeValueMatrixFamily
      A)

theorem exactTarget_of_alternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    ExactTarget :=
  (nonRoleSplitSourceOfAlternativeValueMatrixFamily A).exactTarget

theorem arbitraryTarget_of_fullMetricClosedPlacementWitness
    (W : FullMetricClosedPlacementWitness) :
    ArbitraryTarget :=
  (nonRoleSplitSourceOfFullMetricClosedPlacementWitness W).arbitraryTarget

theorem arbitraryTarget_of_reducedMetricClosedPlacementWitness
    (W : ReducedMetricClosedPlacementWitness) :
    ArbitraryTarget :=
  (nonRoleSplitSourceOfReducedMetricClosedPlacementWitness W).arbitraryTarget

theorem arbitraryTarget_of_freePlacementSourceFields
    (S : MinimalFreePlacementFields) :
    ArbitraryTarget :=
  (nonRoleSplitSourceOfFreePlacementSourceFields S).arbitraryTarget

theorem arbitraryTarget_of_alternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    ArbitraryTarget :=
  (nonRoleSplitSourceOfAlternativeValueMatrixFamily A).arbitraryTarget

end

end NonRoleSplitSourceInhabitationW25
end PachToth

namespace Verified

abbrev PachTothW25NonRoleSplitSource : Type :=
  PachToth.NonRoleSplitSourceInhabitationW25.NonRoleSplitSource

theorem pachtoth_w25_nonempty_nonRoleSplitSource_iff_exactTarget :
    Nonempty PachTothW25NonRoleSplitSource <->
      PachToth.targetUpperConstructionFiveSixteen :=
  PachToth.NonRoleSplitSourceInhabitationW25.nonempty_nonRoleSplitSource_iff_exactTarget

end Verified
end ErdosProblems1066
