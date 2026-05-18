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

/-- Alias exposing the checked remainder route as the fixed-`n` small case
below sixteen. -/
theorem targetUpperConstructionFiveSixteenAt_of_lt_sixteen
    {n : Nat} (hn : n < 16) :
    targetUpperConstructionFiveSixteenAt n :=
  targetUpperConstructionFiveSixteenAt_remainder hn

/-- A quotient exact-chain certificate and the checked finite remainder
certificate discharge the target at an arbitrary vertex count. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChainQuotient
    (n : Nat) (chain : SplitSoundness.ExactChainUpper (n / 16)) :
    targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  have htarget :
      targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) :=
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      chain
      (SplitSoundness.remainderUpperOfConstruction (n % 16))
  rwa [hsplit]

/-- Exact-block target data plus the checked remainder construction gives the
fixed-`n` target.  Positive quotients are supplied only by the exact-target
hypothesis; quotient zero is the empty chain. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n := by
  exact
    targetUpperConstructionFiveSixteenAt_of_exactChainQuotient n
      (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16))

/-- Exact-chain data for the small range below sixteen. -/
def exactChainCertificatesUpToSixteen :
    SmallCaseReduction.ExactChainSmallCaseCertificates 16 where
  chain := by
    intro n hn
    have hdiv : n / 16 = 0 := Nat.div_eq_of_lt hn
    simpa [hdiv] using SplitSoundness.emptyExactChainUpper

/-- Exact-chain data for any cutoff bounded by sixteen. -/
def exactChainCertificatesUpTo_of_le_sixteen
    (N0 : Nat) (hN : N0 <= 16) :
    SmallCaseReduction.ExactChainSmallCaseCertificates N0 where
  chain := by
    intro n hn
    have hn16 : n < 16 := Nat.lt_of_lt_of_le hn hN
    have hdiv : n / 16 = 0 := Nat.div_eq_of_lt hn16
    simpa [hdiv] using SplitSoundness.emptyExactChainUpper

/-- The small-case reduction is discharged for all vertex counts below sixteen. -/
theorem targetUpperConstructionFiveSixteenSmallUpTo_sixteen :
    targetUpperConstructionFiveSixteenSmallUpTo 16 := by
  exact
    SmallCaseReduction.targetUpperConstructionFiveSixteenSmallUpTo_of_exactChainCertificates
      exactChainCertificatesUpToSixteen

/-- The checked remainder certificates discharge every smaller cutoff as well. -/
theorem targetUpperConstructionFiveSixteenSmallUpTo_of_le_sixteen
    {N0 : Nat} (hN : N0 <= 16) :
    targetUpperConstructionFiveSixteenSmallUpTo N0 := by
  exact
    SmallCaseReduction.targetUpperConstructionFiveSixteenSmallUpTo_of_exactChainCertificates
      (exactChainCertificatesUpTo_of_le_sixteen N0 hN)

/-- Exact-block target data supplies exact-chain small-case certificates for
any finite cutoff requested by an eventual arbitrary-`n` route. -/
def exactChainSmallCaseCertificatesOfExactTarget
    (Hexact : targetUpperConstructionFiveSixteen) (N0 : Nat) :
    SmallCaseReduction.ExactChainSmallCaseCertificates N0 where
  chain := by
    intro n _hn
    exact SplitSoundness.exactChainUpperOfTarget Hexact (n / 16)

/-- Exact-block target data discharges the finite small-case obligation at any
cutoff by the checked translated-remainder split. -/
theorem targetUpperConstructionFiveSixteenSmallUpTo_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) (N0 : Nat) :
    targetUpperConstructionFiveSixteenSmallUpTo N0 := by
  intro n _hn
  by_cases hn16 : n < 16
  case pos =>
    exact targetUpperConstructionFiveSixteenAt_of_lt_sixteen hn16
  case neg =>
    exact targetUpperConstructionFiveSixteenAt_of_exactTarget Hexact n

/-- Exact-block target data, paired with the checked below-sixteen
certificates, gives the full arbitrary-`n` target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  by_cases hn16 : n < 16
  case pos =>
    exact targetUpperConstructionFiveSixteenAt_of_lt_sixteen hn16
  case neg =>
    exact targetUpperConstructionFiveSixteenAt_of_exactTarget Hexact n

/-- Callback form of the previous projection, matching the eventual-route
small-case hook.  The supplied large-case theorem is not needed because the
exact-block target already gives the required exact-chain certificates. -/
theorem smallCaseCallback_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) :
    forall N0 : Nat,
      (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
        targetUpperConstructionFiveSixteenSmallUpTo N0 := by
  intro N0 _Hlarge
  exact targetUpperConstructionFiveSixteenSmallUpTo_of_exactTarget Hexact N0

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
