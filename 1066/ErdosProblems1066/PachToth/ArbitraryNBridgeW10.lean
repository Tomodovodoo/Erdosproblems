import ErdosProblems1066.KnownBounds
import ErdosProblems1066.PachToth.ExactRemainderPublicBridge
import ErdosProblems1066.PachToth.PachTothFinalDataAssembly
import ErdosProblems1066.PachToth.SplitArbitraryNNonRigidBridge

set_option autoImplicit false

/-!
# W10 arbitrary-`n` Pach--Toth bridge

This module is an internal routing layer.  It records conditional wrappers
from explicit exact-target packages to the arbitrary-`n` Pach--Toth target,
always using the checked exact/remainder bridge.  It deliberately does not add
any new `KnownBounds` or `Verified` theorem.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNBridgeW10

noncomputable section

open ExactRemainderPublicBridge
open PachTothFinalDataAssembly

universe u

/-- A route row whose arbitrary and fixed-`n` conclusions are obtained from
an explicit exact target and the checked finite remainders. -/
structure CheckedRemainderRouteRow (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- Build a checked-remainder row from any exact-target projection. -/
def checkedRemainderRouteRow
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen) :
    CheckedRemainderRouteRow alpha where
  exactTarget := exactTarget
  fixedTarget := fun a n =>
    ArbitraryNExactRemainderClosure.at_of_exactTarget_checkedRemainder
      (exactTarget a) n
  arbitraryTarget := fun a =>
    targetUpperConstructionFiveSixteenArbitrary_of_exactBlocks_checkedRemainders
      (exactTarget a)

/-- A minimal explicit exact-target package.  The field is still conditional
data, not a proof of the final public Pach--Toth theorem. -/
structure ExactTargetPackage where
  exactTarget : PachToth.targetUpperConstructionFiveSixteen

namespace ExactTargetPackage

/-- Fixed-`n` target from an explicit exact-target package and checked
remainders. -/
theorem targetUpperConstructionFiveSixteenAt_checkedRemainders
    (P : ExactTargetPackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  ArbitraryNExactRemainderClosure.at_of_exactTarget_checkedRemainder
    P.exactTarget n

/-- Arbitrary target from an explicit exact-target package and checked
remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
    (P : ExactTargetPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactBlocks_checkedRemainders
    P.exactTarget

end ExactTargetPackage

/-- Explicit exact-chain certificates for every positive block count. -/
structure PositiveExactChainPackage where
  exactChain :
    forall k : Nat, 0 < k -> SplitSoundness.ExactChainUpper k

namespace PositiveExactChainPackage

/-- Positive exact-chain certificates repackage as the exact Pach--Toth
target. -/
theorem targetUpperConstructionFiveSixteen
    (P : PositiveExactChainPackage) :
    PachToth.targetUpperConstructionFiveSixteen := by
  intro k hk
  exact
    Exists.intro
      (P.exactChain k hk).config
      (P.exactChain k hk).independent_card_le_five_mul

/-- Fixed-`n` target from exact-chain certificates and checked remainders. -/
theorem targetUpperConstructionFiveSixteenAt_checkedRemainders
    (P : PositiveExactChainPackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  ArbitraryNExactRemainderClosure.at_of_exactTarget_checkedRemainder
    P.targetUpperConstructionFiveSixteen n

/-- Arbitrary target from exact-chain certificates and checked remainders,
routed through the public exact/remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
    (P : PositiveExactChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactBlocks_checkedRemainders
    P.targetUpperConstructionFiveSixteen

/-- The same exact-chain package also closes by the split bridge, whose
remainder side is the checked translated construction. -/
theorem targetUpperConstructionFiveSixteenArbitrary_splitBridge
    (P : PositiveExactChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  SplitArbitraryNNonRigidBridge.targetUpperConstructionFiveSixteenArbitrary_of_positiveExactChains
    P.exactChain

end PositiveExactChainPackage

/-- Explicit closed placements for every positive block count. -/
structure ClosedPlacementPackage where
  placement :
    forall k : Nat, forall hk : 0 < k,
      DeformedPlacement.ClosedPlacement k hk

namespace ClosedPlacementPackage

/-- Closed-placement packages supply exact-chain certificates. -/
def toPositiveExactChainPackage
    (P : ClosedPlacementPackage) :
    PositiveExactChainPackage where
  exactChain := fun k hk =>
    SplitArbitraryNNonRigidBridge.exactChainUpperOfClosedPlacement
      (P.placement k hk)

/-- Closed-placement packages repackage as the exact Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen
    (P : ClosedPlacementPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  P.toPositiveExactChainPackage.targetUpperConstructionFiveSixteen

/-- Fixed-`n` target from closed-placement packages and checked remainders. -/
theorem targetUpperConstructionFiveSixteenAt_checkedRemainders
    (P : ClosedPlacementPackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  ArbitraryNExactRemainderClosure.at_of_exactTarget_checkedRemainder
    P.targetUpperConstructionFiveSixteen n

/-- Arbitrary target from closed-placement packages and checked remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
    (P : ClosedPlacementPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactBlocks_checkedRemainders
    P.targetUpperConstructionFiveSixteen

/-- The same closed-placement package closes directly through the non-rigid
split bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_splitBridge
    (P : ClosedPlacementPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  SplitArbitraryNNonRigidBridge.targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    P.placement

end ClosedPlacementPackage

/-- The W10 routing matrix.  Every row is conditional on explicit data; no
row asserts that such data has been constructed unconditionally. -/
structure Matrix where
  exactTargetPackage : CheckedRemainderRouteRow ExactTargetPackage
  positiveExactChains : CheckedRemainderRouteRow PositiveExactChainPackage
  closedPlacements : CheckedRemainderRouteRow ClosedPlacementPackage
  flexibleLowerTables :
    CheckedRemainderRouteRow
      PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily
  flexibleValueMatrices :
    CheckedRemainderRouteRow
      PachTothFinalDataAssembly.FlexiblePeriodValueMatrixFamily
  minimalExactTargetCertificate :
    CheckedRemainderRouteRow
      PachTothW8ClosureMatrix.MinimalExactTargetCertificate
  concreteRemainingData :
    CheckedRemainderRouteRow
      PachTothW8ClosureMatrix.ConcreteRemainingData
  concreteNonConnectorLowerTables :
    CheckedRemainderRouteRow
      ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily
  concreteValueMatrices :
    CheckedRemainderRouteRow
      ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily
  candidateValueMatrices :
    CheckedRemainderRouteRow
      ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily

/-- The checked W10 exact-to-arbitrary routing matrix. -/
def matrix : Matrix where
  exactTargetPackage :=
    checkedRemainderRouteRow ExactTargetPackage.exactTarget
  positiveExactChains :=
    checkedRemainderRouteRow
      PositiveExactChainPackage.targetUpperConstructionFiveSixteen
  closedPlacements :=
    checkedRemainderRouteRow
      ClosedPlacementPackage.targetUpperConstructionFiveSixteen
  flexibleLowerTables :=
    checkedRemainderRouteRow
      PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily.targetUpperConstructionFiveSixteen
  flexibleValueMatrices :=
    checkedRemainderRouteRow
      PachTothFinalDataAssembly.FlexiblePeriodValueMatrixFamily.targetUpperConstructionFiveSixteen
  minimalExactTargetCertificate :=
    checkedRemainderRouteRow
      PachTothFinalDataAssembly.targetUpperConstructionFiveSixteen_of_minimalExactTargetCertificate
  concreteRemainingData :=
    checkedRemainderRouteRow
      PachTothFinalDataAssembly.targetUpperConstructionFiveSixteen_of_concreteRemainingData
  concreteNonConnectorLowerTables :=
    checkedRemainderRouteRow
      targetUpperConstructionFiveSixteen_of_concreteNonConnectorLowerTableFamily
  concreteValueMatrices :=
    checkedRemainderRouteRow
      PachTothFinalDataAssembly.targetUpperConstructionFiveSixteen_of_concreteValueMatrixFamily
  candidateValueMatrices :=
    checkedRemainderRouteRow
      PachTothFinalDataAssembly.targetUpperConstructionFiveSixteen_of_candidateValueMatrixFamily

/-- Fixed-`n` target from the minimal W8 exact-target certificate, routed
through checked remainders. -/
theorem targetUpperConstructionFiveSixteenAt_of_minimalExactTargetCertificate
    (C : PachTothW8ClosureMatrix.MinimalExactTargetCertificate) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.minimalExactTargetCertificate.fixedTarget C n

/-- Arbitrary target from the minimal W8 exact-target certificate, routed
through checked remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_minimalExactTargetCertificate
    (C : PachTothW8ClosureMatrix.MinimalExactTargetCertificate) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.minimalExactTargetCertificate.arbitraryTarget C

/-- Fixed-`n` target from concrete remaining data, routed through checked
remainders. -/
theorem targetUpperConstructionFiveSixteenAt_of_concreteRemainingData
    (D : PachTothW8ClosureMatrix.ConcreteRemainingData) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.concreteRemainingData.fixedTarget D n

/-- Arbitrary target from concrete remaining data, routed through checked
remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteRemainingData
    (D : PachTothW8ClosureMatrix.ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteRemainingData.arbitraryTarget D

/-- Fixed-`n` target from concrete non-connector lower tables, routed through
checked remainders. -/
theorem targetUpperConstructionFiveSixteenAt_of_concreteNonConnectorLowerTableFamily
    (C : ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily)
    (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.concreteNonConnectorLowerTables.fixedTarget C n

/-- Arbitrary target from concrete non-connector lower tables, routed through
checked remainders. -/
theorem
    targetUpperConstructionFiveSixteenArbitrary_of_concreteNonConnectorLowerTableFamily
    (C : ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteNonConnectorLowerTables.arbitraryTarget C

/-- Fixed-`n` target from concrete value matrices, routed through checked
remainders. -/
theorem targetUpperConstructionFiveSixteenAt_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily)
    (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.concreteValueMatrices.fixedTarget C n

/-- Arbitrary target from concrete value matrices, routed through checked
remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteValueMatrices.arbitraryTarget C

/-- Fixed-`n` target from candidate value matrices, routed through checked
remainders. -/
theorem targetUpperConstructionFiveSixteenAt_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily)
    (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.candidateValueMatrices.fixedTarget C n

/-- Arbitrary target from candidate value matrices, routed through checked
remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateValueMatrices.arbitraryTarget C

end

end ArbitraryNBridgeW10
end PachToth
end ErdosProblems1066
