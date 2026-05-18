import ErdosProblems1066.PachToth.AppendedRemainderSeparationInhabitationW25
import ErdosProblems1066.PachToth.NonRoleSplitSourceInhabitationW25

set_option autoImplicit false

/-!
# W26 arbitrary-`n` final assembly for the Pach--Toth route

This file is a narrow assembly layer over the W25 translated-remainder and
non-role split-source routes.  The W25 separation theorem closes the
arbitrary-`n` construction from the exact `16 * k` target by translating the
checked finite remainder far away.  Conversely, the arbitrary-`n` statement
specialized to multiples of `16` gives the exact target by arithmetic.

Thus the remaining dependency for a full arbitrary-`n` theorem is precisely
the exact `16 * k` target, equivalently the inhabited non-role split source
or positive exact-chain package already isolated in W25.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNFinalAssemblyW26

open Arithmetic

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev NonRoleSplitSource : Type :=
  NonRoleSplitSourceInhabitationW25.NonRoleSplitSource

abbrev PositiveExactChainPackage : Type :=
  NonRoleSplitSourceInhabitationW25.PositiveExactChainPackage

theorem ceilDiv_five_mul_sixteen_mul (k : Nat) :
    ceilDiv (5 * (16 * k)) 16 = 5 * k := by
  unfold ceilDiv
  omega

/-! ## Exact target and arbitrary target are now equivalent -/

/-- W25 translated-remainder separation closes arbitrary `n` from the exact
`16 * k` target. -/
theorem arbitraryTarget_of_exactTarget_translatedRemainder
    (H : ExactTarget) :
    ArbitraryTarget :=
  ConcreteRemainderSplitW24.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedRemainder_translatedSeparation
    H

/-- The arbitrary-`n` target restricted to multiples of `16` gives the exact
block target. -/
theorem exactTarget_of_arbitraryTarget
    (H : ArbitraryTarget) :
    ExactTarget := by
  intro k hk
  rcases H (16 * k) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro s hs
  have hbound := hC s hs
  simpa [ceilDiv_five_mul_sixteen_mul k] using hbound

/-- The sharp W26 endpoint: arbitrary `n` is exactly the remaining exact
`16 * k` target. -/
theorem exactTarget_iff_arbitraryTarget :
    ExactTarget <-> ArbitraryTarget := by
  constructor
  · exact arbitraryTarget_of_exactTarget_translatedRemainder
  · exact exactTarget_of_arbitraryTarget

theorem arbitraryTarget_iff_exactTarget :
    ArbitraryTarget <-> ExactTarget :=
  exactTarget_iff_arbitraryTarget.symm

/-! ## Minimal inhabitance dependencies -/

theorem arbitraryTarget_of_nonRoleSplitSource
    (S : NonRoleSplitSource) :
    ArbitraryTarget :=
  NonRoleSplitSourceInhabitationW25.arbitraryTarget_of_nonRoleSplitSource S

theorem nonempty_nonRoleSplitSource_iff_arbitraryTarget :
    Nonempty NonRoleSplitSource <-> ArbitraryTarget :=
  Iff.trans
    NonRoleSplitSourceInhabitationW25.nonempty_nonRoleSplitSource_iff_exactTarget
    exactTarget_iff_arbitraryTarget

theorem arbitraryTarget_of_nonempty_nonRoleSplitSource
    (H : Nonempty NonRoleSplitSource) :
    ArbitraryTarget :=
  nonempty_nonRoleSplitSource_iff_arbitraryTarget.mp H

theorem nonempty_nonRoleSplitSource_of_arbitraryTarget
    (H : ArbitraryTarget) :
    Nonempty NonRoleSplitSource :=
  nonempty_nonRoleSplitSource_iff_arbitraryTarget.mpr H

/-- The smallest exact-chain package isolated in W25 is also exactly the
remaining arbitrary-`n` dependency. -/
theorem nonempty_positiveExactChainPackage_iff_arbitraryTarget :
    Nonempty PositiveExactChainPackage <-> ArbitraryTarget := by
  have hsource :
      Nonempty NonRoleSplitSource <-> Nonempty PositiveExactChainPackage :=
    NonRoleSplitSourceInhabitationW25.nonempty_nonRoleSplitSource_iff_positiveExactChainPackage
  exact Iff.trans hsource.symm nonempty_nonRoleSplitSource_iff_arbitraryTarget

theorem arbitraryTarget_of_positiveExactChainPackage
    (P : PositiveExactChainPackage) :
    ArbitraryTarget :=
  nonempty_positiveExactChainPackage_iff_arbitraryTarget.mp
    (Nonempty.intro P)

/-- Minimal exact dependency, stated without a source structure: proving the
exact `16 * k` construction is both necessary and sufficient for the full
arbitrary-`n` construction. -/
theorem minimalExactDependency :
    ArbitraryTarget <-> ExactTarget :=
  arbitraryTarget_iff_exactTarget

end

end ArbitraryNFinalAssemblyW26
end PachToth

namespace Verified

abbrev PachTothW26ArbitraryNDependency : Prop :=
  Nonempty PachToth.ArbitraryNFinalAssemblyW26.NonRoleSplitSource

theorem pachtoth_w26_arbitraryTarget_iff_exactTarget :
    PachToth.targetUpperConstructionFiveSixteenArbitrary <->
      PachToth.targetUpperConstructionFiveSixteen :=
  PachToth.ArbitraryNFinalAssemblyW26.arbitraryTarget_iff_exactTarget

theorem pachtoth_w26_nonRoleSplitSource_iff_arbitraryTarget :
    PachTothW26ArbitraryNDependency <->
      PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.ArbitraryNFinalAssemblyW26.nonempty_nonRoleSplitSource_iff_arbitraryTarget

end Verified
end ErdosProblems1066
