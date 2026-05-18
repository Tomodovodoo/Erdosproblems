import ErdosProblems1066.PachToth.ArbitraryN
import ErdosProblems1066.PachToth.SplitSoundness
import ErdosProblems1066.PachToth.RemainderConstruction
import ErdosProblems1066.PachToth.RemainderPlacement
import ErdosProblems1066.PachToth.PachTothKnownBoundsFromConcreteRowsW23
import ErdosProblems1066.PachToth.ConcreteValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.CandidateValueMatrixRowPackageInhabitationW23

set_option autoImplicit false

/-!
# W24 arbitrary-`n` Pach--Toth route from non-role sources

This module isolates the smallest non-role-hinge source needed by the checked
arbitrary-`n` split route: exact upper certificates on every positive
`16 * k` chain block.  The finite remainder side is supplied only by the
existing checked `RemainderConstruction` data, and the final bridge is
conditional on an explicit source.

The W23 concrete/candidate row adapters below are also conditional adapters:
they consume row packages or endpoint packages and do not assert that such
packages are inhabited.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNNonRoleSourceW24

open Arithmetic

noncomputable section

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev ConcreteValueMatrixRowPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.ConcreteValueMatrixRowPackage

abbrev CandidateValueMatrixRowPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.CandidateValueMatrixRowPackage

abbrev ConcreteRowsEndpointPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.ConcreteRowsEndpointPackage

abbrev CandidateRowsEndpointPackage : Type :=
  PachTothKnownBoundsFromConcreteRowsW23.CandidateRowsEndpointPackage

/-- Minimal non-role split source: exact upper certificates for all positive
`16 * k` chain blocks.  Small quotients are handled separately by the checked
remainder construction and the empty exact-chain certificate. -/
structure NonRoleSplitSource where
  exactChain : forall k : Nat, 0 < k -> SplitSoundness.ExactChainUpper k

namespace NonRoleSplitSource

/-- Select the positive exact-chain certificate, falling back to the empty
chain when the quotient block is zero. -/
def exactChainAt
    (S : NonRoleSplitSource) (k : Nat) :
    SplitSoundness.ExactChainUpper k := by
  by_cases hk : 0 < k
  case pos =>
    exact S.exactChain k hk
  case neg =>
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    rw [hk0]
    exact SplitSoundness.emptyExactChainUpper

/-- The source repackages as the exact Pach--Toth target on `16 * k` blocks. -/
theorem exactTarget
    (S : NonRoleSplitSource) :
    ExactTarget := by
  intro k hk
  exact
    Exists.intro
      (S.exactChain k hk).config
      (S.exactChain k hk).independent_card_le_five_mul

/-- Fixed target for the canonical `16 * (n / 16) + n % 16` split. -/
theorem fixedTarget_divMod
    (S : NonRoleSplitSource) (n : Nat) :
    FixedTarget (16 * (n / 16) + n % 16) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      (Nat.mod_lt n (by norm_num))
      (S.exactChainAt (n / 16))
      (SplitSoundness.remainderUpperOfConstruction (n % 16))

/-- Fixed target at an arbitrary vertex count, after rewriting by div/mod. -/
theorem fixedTarget
    (S : NonRoleSplitSource) (n : Nat) :
    FixedTarget n := by
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact S.fixedTarget_divMod n

/-- Conditional arbitrary-`n` target from the non-role split source. -/
theorem arbitraryTarget
    (S : NonRoleSplitSource) :
    ArbitraryTarget := by
  intro n
  exact S.fixedTarget n

/-- Any exact Pach--Toth target supplies the minimal non-role split source. -/
def ofExactTarget
    (H : ExactTarget) :
    NonRoleSplitSource where
  exactChain := fun k _hk => SplitSoundness.exactChainUpperOfTarget H k

/-- Exact target plus checked remainders closes the arbitrary target through
the same minimal non-role source. -/
theorem arbitraryTarget_ofExactTarget
    (H : ExactTarget) :
    ArbitraryTarget :=
  (ofExactTarget H).arbitraryTarget

/-- Concrete W23 row packages provide the non-role split source through their
checked exact target projection. -/
def ofConcreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    NonRoleSplitSource :=
  ofExactTarget
    (PachTothKnownBoundsFromConcreteRowsW23.targetUpperConstructionFiveSixteen_of_concreteValueMatrixRowPackage
      P)

/-- Candidate W23 row packages provide the non-role split source through their
checked exact target projection. -/
def ofCandidateValueMatrixRowPackage
    (P : CandidateValueMatrixRowPackage) :
    NonRoleSplitSource :=
  ofExactTarget
    (PachTothKnownBoundsFromConcreteRowsW23.targetUpperConstructionFiveSixteen_of_candidateValueMatrixRowPackage
      P)

/-- Concrete endpoint packages provide the non-role split source. -/
def ofConcreteRowsEndpointPackage
    (P : ConcreteRowsEndpointPackage) :
    NonRoleSplitSource :=
  ofExactTarget P.exactTarget

/-- Candidate endpoint packages provide the non-role split source. -/
def ofCandidateRowsEndpointPackage
    (P : CandidateRowsEndpointPackage) :
    NonRoleSplitSource :=
  ofExactTarget P.exactTarget

theorem arbitraryTarget_ofConcreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ArbitraryTarget :=
  (ofConcreteValueMatrixRowPackage P).arbitraryTarget

theorem arbitraryTarget_ofCandidateValueMatrixRowPackage
    (P : CandidateValueMatrixRowPackage) :
    ArbitraryTarget :=
  (ofCandidateValueMatrixRowPackage P).arbitraryTarget

theorem arbitraryTarget_ofConcreteRowsEndpointPackage
    (P : ConcreteRowsEndpointPackage) :
    ArbitraryTarget :=
  (ofConcreteRowsEndpointPackage P).arbitraryTarget

theorem arbitraryTarget_ofCandidateRowsEndpointPackage
    (P : CandidateRowsEndpointPackage) :
    ArbitraryTarget :=
  (ofCandidateRowsEndpointPackage P).arbitraryTarget

end NonRoleSplitSource

/-! ## Public conditional bridges -/

theorem targetUpperConstructionFiveSixteenArbitrary_of_nonRoleSplitSource
    (S : NonRoleSplitSource) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  S.arbitraryTarget

theorem targetUpperConstructionFiveSixteenAt_of_nonRoleSplitSource
    (S : NonRoleSplitSource) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  S.fixedTarget n

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_nonRole
    (H : PachToth.targetUpperConstructionFiveSixteen) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  NonRoleSplitSource.arbitraryTarget_ofExactTarget H

theorem targetUpperConstructionFiveSixteenArbitrary_of_w23_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  NonRoleSplitSource.arbitraryTarget_ofConcreteValueMatrixRowPackage P

theorem targetUpperConstructionFiveSixteenArbitrary_of_w23_candidateValueMatrixRowPackage
    (P : CandidateValueMatrixRowPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  NonRoleSplitSource.arbitraryTarget_ofCandidateValueMatrixRowPackage P

theorem targetUpperConstructionFiveSixteenArbitrary_of_w23_concreteRowsEndpointPackage
    (P : ConcreteRowsEndpointPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  NonRoleSplitSource.arbitraryTarget_ofConcreteRowsEndpointPackage P

theorem targetUpperConstructionFiveSixteenArbitrary_of_w23_candidateRowsEndpointPackage
    (P : CandidateRowsEndpointPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  NonRoleSplitSource.arbitraryTarget_ofCandidateRowsEndpointPackage P

/-- The split-source route agrees with the existing W23 known-bound endpoint
on its arbitrary-target conclusion, but is proved through exact chains plus
checked remainders. -/
theorem concreteRowsEndpoint_nonRole_arbitraryTarget
    (P : ConcreteRowsEndpointPackage) :
    targetUpperConstructionFiveSixteenArbitrary_of_w23_concreteRowsEndpointPackage
      P =
      P.arbitraryTarget := by
  rfl

/-- Candidate endpoint analogue of the concrete endpoint bridge. -/
theorem candidateRowsEndpoint_nonRole_arbitraryTarget
    (P : CandidateRowsEndpointPackage) :
    targetUpperConstructionFiveSixteenArbitrary_of_w23_candidateRowsEndpointPackage
      P =
      P.arbitraryTarget := by
  rfl

end

end ArbitraryNNonRoleSourceW24
end PachToth
end ErdosProblems1066
