import ErdosProblems1066.PachToth.ArbitraryNClosureCandidate
import ErdosProblems1066.PachToth.RemainderConstruction
import ErdosProblems1066.PachToth.RemainderPlacement
import ErdosProblems1066.PachToth.SplitSoundness
import ErdosProblems1066.PachToth.SplitRealizationFinal

set_option autoImplicit false

/-!
# Arbitrary-`n` closure from exact blocks and checked remainders

This module gives short reusable wrappers for the final Pach--Toth
arbitrary-`n` split:

* exact target data supplies the `16 * k` chain certificate;
* the checked finite remainder construction supplies the `r < 16` certificate;
* the existing translated-remainder placement and split soundness close
  `16 * k + r`, hence every `n` by div/mod.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNExactRemainderClosure

open Arithmetic

noncomputable section

/-- The checked finite remainder construction, packaged in the split-soundness
certificate type for the `n % 16` remainder range. -/
def checkedRemainderUpperOfLtSixteen {r : Nat} (_hr : r < 16) :
    SplitSoundness.RemainderUpper r where
  config :=
    Classical.choose (RemainderConstruction.exists_remainder_config_mod_sixteen _hr)
  independent_card_le_ceil_third :=
    Classical.choose_spec
      (RemainderConstruction.exists_remainder_config_mod_sixteen _hr)

/-- Exact target data supplies the split-soundness exact-chain certificate for
the `16 * k` block. -/
def exactChainUpperOfExactTarget
    (Hexact : targetUpperConstructionFiveSixteen) (k : Nat) :
    SplitSoundness.ExactChainUpper k :=
  SplitSoundness.exactChainUpperOfTarget Hexact k

/-- Exact `16 * k` target data and a checked `r < 16` remainder close the
target at the split vertex count `16 * k + r`. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder
    (Hexact : targetUpperConstructionFiveSixteen) {k r : Nat} (hr : r < 16) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      (exactChainUpperOfExactTarget Hexact k)
      (checkedRemainderUpperOfLtSixteen hr)

/-- Div/mod form of the exact-target plus checked-remainder split. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_divMod
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact
    targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder
      Hexact hr

/-- Exact `16 * k` target data gives the arbitrary-`n` Pach--Toth target via
the checked `r < 16` remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedRemainder
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  exact
    targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_divMod
      Hexact n

/-- Fixed-`n` facade matching the arbitrary-`n` closure candidate shape. -/
theorem at_of_exactTarget_checkedRemainder
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_divMod
    Hexact n

/-- Arbitrary-`n` facade matching the closure candidate shape. -/
theorem arbitrary_of_exactTarget_checkedRemainder
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedRemainder
    Hexact

/-- The existing candidate closure is recovered from the same exact-target
plus checked-remainder wrapper. -/
theorem arbitraryNClosureCandidate_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    arbitrary_of_exactTarget_checkedRemainder Hexact

end

end ArbitraryNExactRemainderClosure
end PachToth
end ErdosProblems1066
