import ErdosProblems1066.PachToth.ClosedChainReduction

set_option autoImplicit false

/-!
# Eventual closed-placement reduction

This module records the final pure routing step from eventual explicit
closed-placement certificates, together with the matching finite small-case
checks, to the arbitrary-`n` Pach--Toth target.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedChainReduction

noncomputable section

/-- Eventual explicit closed-placement certificates, plus the finite small cases
below the eventual threshold they produce, imply the arbitrary-`n`
Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualExplicitClosedPlacement_and_small
    (K0 : Nat)
    (Hclosed :
      forall (k : Nat), K0 <= k -> forall hk : 0 < k,
        ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk)
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  match
    targetUpperConstructionFiveSixteenEventually_of_eventualExplicitClosedPlacementCertificates
      K0 Hclosed with
  | Exists.intro N0 Hlarge =>
      exact
        targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
          N0 Hlarge (Hsmall N0 Hlarge)

end

end ClosedChainReduction
end PachToth
end ErdosProblems1066
