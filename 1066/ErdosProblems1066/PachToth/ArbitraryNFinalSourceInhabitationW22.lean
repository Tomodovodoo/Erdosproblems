import ErdosProblems1066.PachToth.ArbitraryNInputPackageRouteW21
import ErdosProblems1066.PachToth.ConcreteValueMatrixToInputPackageW21
import ErdosProblems1066.PachToth.ExactRemainderPublicBridge
import ErdosProblems1066.PachToth.SplitSoundnessInstantiationW13

set_option autoImplicit false

/-!
# W22 arbitrary-n final source inhabitation

This file keeps the final source question focused on the W21
`KnownBoundsRemainingData`, which is definitionally the W19 input package.
It records the concrete value-matrix inhabitant route when that named package
is supplied, and otherwise reduces arbitrary-n finality to the exact-block
target plus the already checked remainder split.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNFinalSourceInhabitationW22

noncomputable section

abbrev W19InputPackage : Type :=
  ArbitraryNInputPackageRouteW21.W19InputPackage

abbrev KnownBoundsRemainingData : Type :=
  ArbitraryNInputPackageRouteW21.KnownBoundsRemainingData

abbrev W20SourceFields : Type :=
  ArbitraryNInputPackageRouteW21.W20SourceFields

abbrev ExactTarget : Prop :=
  ArbitraryNInputPackageRouteW21.ExactTarget

abbrev ArbitraryTarget : Prop :=
  ArbitraryNInputPackageRouteW21.ArbitraryTarget

abbrev FixedTarget (n : Nat) : Prop :=
  ArbitraryNInputPackageRouteW21.FixedTarget n

abbrev ExactBlockBound (k : Nat) : Prop :=
  Exists fun C : _root_.UDConfig (16 * k) =>
    forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k

abbrev ArbitraryBound (n : Nat) : Prop :=
  Exists fun C : _root_.UDConfig n =>
    forall s : Finset (Fin n), C.IsIndep s ->
      s.card <= Arithmetic.ceilDiv (5 * n) 16

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteValueMatrixToInputPackageW21.ConcreteValueMatrixFamily

/-! ## Direct W19/KnownBounds data routes -/

/-- Choose the W19 input package carried by nonempty W21 remaining data. -/
def inputPackageOfKnownBoundsRemainingData
    (H : Nonempty KnownBoundsRemainingData) :
    W19InputPackage :=
  Classical.choice H

/-- Raw W20 source fields produce the W21 remaining datum through the W21
input-package route. -/
def knownBoundsRemainingDataOfW20SourceFields
    (S : W20SourceFields) :
    KnownBoundsRemainingData :=
  S.toInputPackage

theorem nonempty_knownBoundsRemainingData_of_w20SourceFields
    (S : W20SourceFields) :
    Nonempty KnownBoundsRemainingData :=
  Nonempty.intro (knownBoundsRemainingDataOfW20SourceFields S)

/-- Concrete value matrices, once supplied, actually inhabit the W19 input
package used by the W21 KnownBounds gate. -/
def knownBoundsRemainingDataOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    KnownBoundsRemainingData :=
  ConcreteValueMatrixToInputPackageW21.inputPackageOfConcreteValueMatrixFamily
    C

theorem nonempty_knownBoundsRemainingData_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    Nonempty KnownBoundsRemainingData :=
  Nonempty.intro (knownBoundsRemainingDataOfConcreteValueMatrixFamily C)

/-! ## Exact-block source as the minimal arbitrary-n finality source -/

/-- W21 remaining data gives the exact-block target through the existing W21
exact-block wrapper. -/
theorem exactTarget_of_knownBoundsRemainingData
    (H : Nonempty KnownBoundsRemainingData) :
    ExactTarget := by
  intro k hk
  exact
    ArbitraryNInputPackageRouteW21.upper_bound_five_sixteen_exact_of_knownBoundsRemainingData
      H k hk

/-- The exact and arbitrary Pach-Toth final targets carry the same finality
information once the checked remainders are available. -/
theorem arbitraryTarget_iff_exactTarget_checkedRemainders :
    ArbitraryTarget <-> ExactTarget := by
  constructor
  case mp =>
    intro Harbitrary k _hk
    let chain :=
      SplitSoundnessInstantiationW13.exactChainUpperOfExactBlockTarget
        (Harbitrary (16 * k))
    exact Exists.intro chain.config chain.independent_card_le_five_mul
  case mpr =>
    intro Hexact
    exact
      ExactRemainderPublicBridge.targetUpperConstructionFiveSixteenArbitrary_of_exactBlocks_checkedRemainders
        Hexact

/-- W21 remaining data gives arbitrary-n finality by first extracting the
exact-block target, then using the checked exact/remainder split. -/
theorem arbitraryTarget_of_knownBoundsRemainingData_checkedRemainders
    (H : Nonempty KnownBoundsRemainingData) :
    ArbitraryTarget :=
  arbitraryTarget_iff_exactTarget_checkedRemainders.2
    (exactTarget_of_knownBoundsRemainingData H)

theorem fixedTarget_of_knownBoundsRemainingData_checkedRemainders
    (H : Nonempty KnownBoundsRemainingData) (n : Nat) :
    FixedTarget n :=
  arbitraryTarget_of_knownBoundsRemainingData_checkedRemainders H n

theorem upper_bound_five_sixteen_arbitrary_of_knownBoundsRemainingData_checkedRemainders
    (H : Nonempty KnownBoundsRemainingData) (n : Nat) :
    ArbitraryBound n :=
  fixedTarget_of_knownBoundsRemainingData_checkedRemainders H n

/-- Concrete value matrices close the W21 KnownBounds remaining-data gate and
then close arbitrary n via the exact/remainder route. -/
theorem arbitraryTarget_of_concreteValueMatrixFamily_checkedRemainders
    (C : ConcreteValueMatrixFamily) :
    ArbitraryTarget :=
  arbitraryTarget_of_knownBoundsRemainingData_checkedRemainders
    (nonempty_knownBoundsRemainingData_of_concreteValueMatrixFamily C)

theorem upper_bound_five_sixteen_arbitrary_of_concreteValueMatrixFamily_checkedRemainders
    (C : ConcreteValueMatrixFamily) (n : Nat) :
    ArbitraryBound n :=
  arbitraryTarget_of_concreteValueMatrixFamily_checkedRemainders C n

end

end ArbitraryNFinalSourceInhabitationW22
end PachToth

namespace Verified

abbrev PachTothW22KnownBoundsRemainingData : Type :=
  PachToth.ArbitraryNFinalSourceInhabitationW22.KnownBoundsRemainingData

abbrev PachTothW22ConcreteValueMatrixFamily : Type :=
  PachToth.ArbitraryNFinalSourceInhabitationW22.ConcreteValueMatrixFamily

theorem pachtoth_w22_arbitraryTarget_iff_exactTarget_checkedRemainders :
    PachToth.targetUpperConstructionFiveSixteenArbitrary <->
      PachToth.targetUpperConstructionFiveSixteen :=
  PachToth.ArbitraryNFinalSourceInhabitationW22.arbitraryTarget_iff_exactTarget_checkedRemainders

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w22_knownBoundsRemainingData
    (H : Nonempty PachTothW22KnownBoundsRemainingData) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.ArbitraryNFinalSourceInhabitationW22.upper_bound_five_sixteen_arbitrary_of_knownBoundsRemainingData_checkedRemainders
    H n

theorem nonempty_pachtoth_w22_knownBoundsRemainingData_of_concreteValueMatrixFamily
    (C : PachTothW22ConcreteValueMatrixFamily) :
    Nonempty PachTothW22KnownBoundsRemainingData :=
  PachToth.ArbitraryNFinalSourceInhabitationW22.nonempty_knownBoundsRemainingData_of_concreteValueMatrixFamily
    C

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w22_concreteValueMatrixFamily
    (C : PachTothW22ConcreteValueMatrixFamily) (n : Nat) :
    Exists fun U : _root_.UDConfig n =>
      forall s : Finset (Fin n), U.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.ArbitraryNFinalSourceInhabitationW22.upper_bound_five_sixteen_arbitrary_of_concreteValueMatrixFamily_checkedRemainders
    C n

end Verified
end ErdosProblems1066
