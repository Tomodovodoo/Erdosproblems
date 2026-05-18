import ErdosProblems1066.PachToth.SmallCaseReduction
import ErdosProblems1066.PachToth.RemainderConstruction
import ErdosProblems1066.PachToth.RemainderPlacement

set_option autoImplicit false

/-!
# Pach--Toth small remainder certificates

This module instantiates the checked translated-remainder split for the
small range `r < 16`.  In this range the chain quotient is zero, so the
empty exact-chain certificate combines with the checked remainder
configuration.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallCaseCertificates

noncomputable section

/-- Every remainder `r < 16` already satisfies the Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteenAt_remainder
    {r : Nat} (hr : r < 16) :
    targetUpperConstructionFiveSixteenAt r := by
  have h :
      targetUpperConstructionFiveSixteenAt (16 * 0 + r) :=
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      (k := 0)
      (r := r)
      hr
      SplitSoundness.emptyExactChainUpper
      (SplitSoundness.remainderUpperOfConstruction r)
  simpa using h

/-- Exact-chain data for the small range below sixteen. -/
def exactChainCertificatesUpToSixteen :
    SmallCaseReduction.ExactChainSmallCaseCertificates 16 where
  chain := by
    intro n hn
    have hdiv : n / 16 = 0 := Nat.div_eq_of_lt hn
    simpa [hdiv] using SplitSoundness.emptyExactChainUpper

/-- The small-case reduction is discharged for all vertex counts below sixteen. -/
theorem targetUpperConstructionFiveSixteenSmallUpTo_sixteen :
    targetUpperConstructionFiveSixteenSmallUpTo 16 := by
  exact
    SmallCaseReduction.targetUpperConstructionFiveSixteenSmallUpTo_of_exactChainCertificates
      exactChainCertificatesUpToSixteen

theorem targetUpperConstructionFiveSixteenAt_r0 :
    targetUpperConstructionFiveSixteenAt 0 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 0) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r1 :
    targetUpperConstructionFiveSixteenAt 1 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 1) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r2 :
    targetUpperConstructionFiveSixteenAt 2 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 2) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r3 :
    targetUpperConstructionFiveSixteenAt 3 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 3) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r4 :
    targetUpperConstructionFiveSixteenAt 4 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 4) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r5 :
    targetUpperConstructionFiveSixteenAt 5 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 5) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r6 :
    targetUpperConstructionFiveSixteenAt 6 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 6) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r7 :
    targetUpperConstructionFiveSixteenAt 7 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 7) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r8 :
    targetUpperConstructionFiveSixteenAt 8 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 8) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r9 :
    targetUpperConstructionFiveSixteenAt 9 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 9) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r10 :
    targetUpperConstructionFiveSixteenAt 10 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 10) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r11 :
    targetUpperConstructionFiveSixteenAt 11 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 11) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r12 :
    targetUpperConstructionFiveSixteenAt 12 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 12) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r13 :
    targetUpperConstructionFiveSixteenAt 13 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 13) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r14 :
    targetUpperConstructionFiveSixteenAt 14 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 14) (by norm_num)

theorem targetUpperConstructionFiveSixteenAt_r15 :
    targetUpperConstructionFiveSixteenAt 15 := by
  exact targetUpperConstructionFiveSixteenAt_remainder (r := 15) (by norm_num)

end

end SmallCaseCertificates
end PachToth
end ErdosProblems1066
