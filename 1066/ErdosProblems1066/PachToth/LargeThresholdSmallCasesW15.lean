import ErdosProblems1066.PachToth.LargeSmallCaseClosureW14
import ErdosProblems1066.PachToth.ArbitraryNEndpointW14
import ErdosProblems1066.PachToth.SmallCaseCertificates

set_option autoImplicit false

/-!
# W15 large-threshold small cases

This module sharpens the finite complement required by the large
closed-placement threshold route.  A vertex-level small complement below
`16 * K0` is exactly enough to recover the missing exact block targets
`16 * k` for `0 < k < K0`; large closed-placement fields supply the remaining
block targets from `K0` onward.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeThresholdSmallCasesW15

open Arithmetic
open LargeSmallCaseClosureW14

noncomputable section

abbrev ExactTarget : Prop :=
  LargeSmallCaseClosureW14.ExactTarget

abbrev EventualTarget : Prop :=
  LargeSmallCaseClosureW14.EventualTarget

abbrev ArbitraryTarget : Prop :=
  LargeSmallCaseClosureW14.ArbitraryTarget

abbrev ExactBlockTarget (k : Nat) : Prop :=
  LargeSmallCaseClosureW14.ExactBlockTarget k

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeSmallCaseClosureW14.LargeClosedPlacementFields K0

abbrev SmallComplement (K0 : Nat) : Prop :=
  targetUpperConstructionFiveSixteenSmallUpTo (16 * K0)

/-! ## Vertex small complements as block complements -/

/-- A vertex-level small complement below `16 * K0` includes every missing
exact block target `16 * k` with `0 < k < K0`. -/
theorem exactBlockTarget_of_smallComplement
    {K0 k : Nat} (small : SmallComplement K0)
    (hklt : k < K0) (_hk : 0 < k) :
    ExactBlockTarget k := by
  have hsmall : 16 * k < 16 * K0 := by
    omega
  exact small (16 * k) hsmall

/-- Repackage a vertex-level small complement as the W14 exact-block threshold
evidence. -/
def exactBlockThresholdEvidenceOfSmallComplement
    {K0 : Nat} (small : SmallComplement K0) :
    ExactBlockThresholdEvidence K0 where
  exactBlock := fun _k hklt hk =>
    exactBlockTarget_of_smallComplement small hklt hk

/-- Repackage a vertex-level small complement as exact-chain threshold
evidence. -/
def exactChainThresholdEvidenceOfSmallComplement
    {K0 : Nat} (small : SmallComplement K0) :
    ExactChainThresholdEvidence K0 :=
  (exactBlockThresholdEvidenceOfSmallComplement small).toExactChainThresholdEvidence

/-- The block-target finite complement and the vertex-level small complement
are equivalent at the large threshold. -/
theorem smallComplement_iff_exactBlockThresholdEvidence (K0 : Nat) :
    SmallComplement K0 <-> ExactBlockThresholdEvidence K0 := by
  constructor
  case mp =>
    intro small
    exact exactBlockThresholdEvidenceOfSmallComplement small
  case mpr =>
    intro E
    exact ExactBlockThresholdEvidence.targetUpperConstructionFiveSixteenSmallUpTo E

/-! ## Large fields with a vertex-level finite complement -/

/-- Large closed-placement fields plus a vertex-level small complement supply
exact block targets on both sides of the threshold. -/
theorem exactBlockTarget_of_largeClosedPlacementFields_smallComplement
    {K0 k : Nat} (L : LargeClosedPlacementFields K0)
    (small : SmallComplement K0) (hk : 0 < k) :
    ExactBlockTarget k := by
  by_cases hK : K0 <= k
  case pos =>
    exact exactBlockTarget_largeClosedPlacementFields L hK hk
  case neg =>
    exact exactBlockTarget_of_smallComplement
      small (Nat.lt_of_not_ge hK) hk

/-- Large closed-placement fields plus the exact finite vertex complement
close the exact block-form target. -/
theorem exactTarget_of_largeClosedPlacementFields_smallComplement
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (small : SmallComplement K0) :
    ExactTarget := by
  exact
    targetUpperConstructionFiveSixteen_of_exactBlockTargets
      (fun k hk =>
        exactBlockTarget_of_largeClosedPlacementFields_smallComplement
          L small hk)

/-- The same data closes the arbitrary-`n` target through the checked
remainder route. -/
theorem arbitraryTarget_of_largeClosedPlacementFields_smallComplement
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (small : SmallComplement K0) :
    ArbitraryTarget := by
  exact
    LargeWithSmallComplementFields.targetUpperConstructionFiveSixteenArbitrary
      { large := L, small := small }

/-- The large closed-placement threshold remains available separately from
the finite complement. -/
theorem eventualTarget_of_largeClosedPlacementFields_smallComplement
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (_small : SmallComplement K0) :
    EventualTarget :=
  eventualTarget_largeClosedPlacementFields L

/-- A compact W15 package: large threshold data plus exactly the vertex-level
finite complement below that threshold. -/
structure LargeWithThresholdSmallCases (K0 : Nat) where
  large : LargeClosedPlacementFields K0
  small : SmallComplement K0

namespace LargeWithThresholdSmallCases

def toSmallComplementFields
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0) :
    LargeWithSmallComplementFields K0 where
  large := P.large
  small := P.small

def toExactBlockComplementFields
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0) :
    LargeWithExactBlockComplementFields K0 where
  large := P.large
  exactBlockBelowThreshold :=
    exactBlockThresholdEvidenceOfSmallComplement P.small

def toArbitraryNEndpointSmallExactBlocks
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0) :
    ArbitraryNEndpointW14.LargeClosedPlacement.WithSmallExactBlocks K0 where
  large := P.large
  smallExactBlocks := fun _k hklt hk =>
    exactBlockTarget_of_smallComplement P.small hklt hk

theorem exactBlockTarget
    {K0 k : Nat} (P : LargeWithThresholdSmallCases K0)
    (hk : 0 < k) :
    ExactBlockTarget k :=
  exactBlockTarget_of_largeClosedPlacementFields_smallComplement
    P.large P.small hk

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0) :
    ExactTarget :=
  exactTarget_of_largeClosedPlacementFields_smallComplement P.large P.small

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0) :
    EventualTarget :=
  eventualTarget_of_largeClosedPlacementFields_smallComplement P.large P.small

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0) :
    ArbitraryTarget :=
  arbitraryTarget_of_largeClosedPlacementFields_smallComplement P.large P.small

theorem exact_eventual_arbitrary
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget := by
  exact
    And.intro
      P.targetUpperConstructionFiveSixteen
      (And.intro
        P.targetUpperConstructionFiveSixteenEventually
        P.targetUpperConstructionFiveSixteenArbitrary)

end LargeWithThresholdSmallCases

/-! ## Small thresholds -/

/-- If the large threshold is at most one block, the required finite
complement is empty apart from the already checked below-sixteen remainders. -/
theorem smallComplement_atMostOne
    {K0 : Nat} (hK0 : K0 <= 1) :
    SmallComplement K0 := by
  exact
    SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_of_le_sixteen
      (by omega)

/-- At threshold at most one, large closed-placement fields close the W15
package without any extra positive block data below the threshold. -/
def largeWithThresholdSmallCases_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    LargeWithThresholdSmallCases K0 where
  large := L
  small := smallComplement_atMostOne hK0

theorem exact_eventual_arbitrary_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (largeWithThresholdSmallCases_atMostOne L hK0).exact_eventual_arbitrary

end

end LargeThresholdSmallCasesW15
end PachToth
end ErdosProblems1066
