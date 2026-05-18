import ErdosProblems1066.PachToth.ArbitraryNExactRemainderClosure

set_option autoImplicit false

/-!
# Public exact/remainder bridge for Pach-Toth

This module gives `KnownBounds`-style conditional wrappers for the
Pach-Toth exact-block target.  It deliberately exposes the exact `16 * k`
target as an explicit hypothesis and only derives fixed-`n` and arbitrary-`n`
wrappers by routing through the checked finite remainders.

No unconditional Pach-Toth final theorem is declared here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactRemainderPublicBridge

noncomputable section

/-- Public exact-block wrapper: the exact `16 * k` construction remains an
explicit hypothesis. -/
theorem upper_bound_five_sixteen_exactBlocks
    (Hexact : targetUpperConstructionFiveSixteen) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  Hexact k hk

/-- Public fixed-`n` wrapper from exact `16 * k` data plus the checked
remainders. -/
theorem upper_bound_five_sixteen_at_of_exactBlocks_checkedRemainders
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 := by
  exact
    ArbitraryNExactRemainderClosure.at_of_exactTarget_checkedRemainder
      Hexact n

/-- Public arbitrary-`n` wrapper from exact `16 * k` data plus the checked
remainders, stated directly in the underlying proposition-valued target
format. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactBlocks_checkedRemainders
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    ArbitraryNExactRemainderClosure.arbitrary_of_exactTarget_checkedRemainder
      Hexact

/-- Public arbitrary-`n` wrapper in the same direct existential style as
`KnownBounds`: the exact-block construction is still an explicit hypothesis. -/
theorem upper_bound_five_sixteen_arbitrary_of_exactBlocks_checkedRemainders
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactBlocks_checkedRemainders
      Hexact n

end

end ExactRemainderPublicBridge
end PachToth
end ErdosProblems1066
