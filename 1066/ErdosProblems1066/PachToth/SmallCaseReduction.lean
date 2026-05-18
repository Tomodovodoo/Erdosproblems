import ErdosProblems1066.PachToth.RemainderPlacement

set_option autoImplicit false

/-!
# Pach--Toth small-case reduction

This module packages the finite small-case obligation used by the eventual
arbitrary-`n` reductions.  It does not enumerate small values.  Instead, the
finite certificates remain explicit: for each `n < N0`, the caller supplies
the exact-chain upper certificate for the quotient block count `n / 16`.
The existing translated-remainder construction supplies the `n % 16`
vertices.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallCaseReduction

noncomputable section

/-- Explicit finite data sufficient for all Pach--Toth small cases below
`N0`.

For each small vertex count `n`, the certificate is an upper construction on
the exact `16 * (n / 16)` chain part.  The remainder part is supplied by the
checked finite remainder construction. -/
structure ExactChainSmallCaseCertificates (N0 : Nat) where
  chain :
    forall n : Nat, n < N0 -> SplitSoundness.ExactChainUpper (n / 16)

/-- Exact-chain small-case certificates imply the `targetUpper...SmallUpTo`
obligation.  The proof is just the existing exact-chain plus translated
remainder bridge, with the finite certificate family left as an explicit
hypothesis. -/
theorem targetUpperConstructionFiveSixteenSmallUpTo_of_exactChainCertificates
    {N0 : Nat} (C : ExactChainSmallCaseCertificates N0) :
    targetUpperConstructionFiveSixteenSmallUpTo N0 := by
  intro n hn
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  have htarget :
      targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) :=
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      (C.chain n hn)
      (SplitSoundness.remainderUpperOfConstruction (n % 16))
  rwa [hsplit]

/-- Adapter for final reductions whose small-case hook is phrased as a
callback receiving the eventual large-case theorem.  The large-case argument is
not needed here because all finite small certificates are supplied directly. -/
theorem smallCaseCallback_of_exactChainCertificates
    (C : forall N0 : Nat, ExactChainSmallCaseCertificates N0) :
    forall N0 : Nat,
      (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
        targetUpperConstructionFiveSixteenSmallUpTo N0 := by
  intro N0 _Hlarge
  exact targetUpperConstructionFiveSixteenSmallUpTo_of_exactChainCertificates
    (C N0)

end

end SmallCaseReduction
end PachToth
end ErdosProblems1066
