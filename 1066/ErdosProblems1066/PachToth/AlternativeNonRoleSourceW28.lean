import ErdosProblems1066.PachToth.NonRoleSplitSourceConstructionW26
import ErdosProblems1066.PachToth.PositiveExactChainAssemblyW27
import ErdosProblems1066.PachToth.RemainderExactSourceConstructionW27
import ErdosProblems1066.PachToth.PachTothW27FinalAssembly

set_option autoImplicit false

/-!
# W28 alternative non-role source route

The W27 concrete lower-table lane is blocked by its period-search dependency.
This file records the independent route that remains live: positive exact
chains, the W26 non-role source, and the W27 translated-remainder source
package.  Endpoint theorems are only projected downstream from those source
fields.
-/

namespace ErdosProblems1066
namespace PachToth
namespace AlternativeNonRoleSourceW28

noncomputable section

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainAssemblyW27.PositiveExactChainPackage

abbrev MinimalExactSourcePackage : Type :=
  PositiveExactChainAssemblyW27.MinimalExactSourcePackage

abbrev ExposedExactChainSource : Type :=
  PositiveExactChainAssemblyW27.ExposedExactChainSource

abbrev NonRoleSplitSource : Type :=
  PositiveExactChainAssemblyW27.NonRoleSplitSource

abbrev RemainderExactSourcePackage : Type :=
  RemainderExactSourceConstructionW27.RemainderExactSourcePackage

abbrev RemainderExactSourceAt
    (P : PositiveExactChainPackage) (n : Nat) : Type :=
  RemainderExactSourceConstructionW27.RemainderExactSourceAt P n

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveExactChainAssemblyW27.ExactBlocksOneThroughFive

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveExactChainAssemblyW27.RemainingPositiveExactChainBlocker

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  PachTothW27FinalAssembly.ConcreteNonConnectorLowerTableFamily

abbrev SmallestConcreteSourceDependency : Type :=
  PachTothW27FinalAssembly.SmallestConcreteSourceDependency

/-! ## Source package, independent of the blocked lower-table lane -/

/-- Exposed exact-chain data together with the translated-remainder split
package that it generates. -/
structure AlternativeNonRoleSourcePackage where
  exposed : ExposedExactChainSource
  remainder : RemainderExactSourcePackage
  remainder_exact_eq :
    remainder.exact =
      PositiveExactChainAssemblyW27.packageOfExposedExactChainSource exposed

def positiveExactChainPackageOfAlternative
    (S : AlternativeNonRoleSourcePackage) :
    PositiveExactChainPackage :=
  PositiveExactChainAssemblyW27.packageOfExposedExactChainSource S.exposed

def minimalExactSourcePackageOfAlternative
    (S : AlternativeNonRoleSourcePackage) :
    MinimalExactSourcePackage :=
  S.exposed.minimalExactSource

def nonRoleSplitSourceOfAlternative
    (S : AlternativeNonRoleSourcePackage) :
    NonRoleSplitSource :=
  PositiveExactChainAssemblyW27.nonRoleSplitSourceOfExposedExactChainSource
    S.exposed

def remainderExactSourcePackageOfAlternative
    (S : AlternativeNonRoleSourcePackage) :
    RemainderExactSourcePackage :=
  S.remainder

def sourceAt
    (S : AlternativeNonRoleSourcePackage) (n : Nat) :
    RemainderExactSourceAt (positiveExactChainPackageOfAlternative S) n := by
  simpa [positiveExactChainPackageOfAlternative, S.remainder_exact_eq]
    using S.remainder.source n

def alternativeOfExposedExactChainSource
    (S : ExposedExactChainSource) :
    AlternativeNonRoleSourcePackage where
  exposed := S
  remainder :=
    RemainderExactSourceConstructionW27.packageOfExactSource
      (PositiveExactChainAssemblyW27.packageOfExposedExactChainSource S)
  remainder_exact_eq := rfl

def alternativeOfPositiveExactChainPackage
    (P : PositiveExactChainPackage) :
    AlternativeNonRoleSourcePackage :=
  alternativeOfExposedExactChainSource
    (PositiveExactChainAssemblyW27.exposedExactChainSourceOfPackage P)

def alternativeOfMinimalExactSourcePackage
    (P : MinimalExactSourcePackage) :
    AlternativeNonRoleSourcePackage :=
  alternativeOfExposedExactChainSource
    (PositiveExactChainAssemblyW27.exposedExactChainSourceOfMinimal P)

def alternativeOfNonRoleSplitSource
    (S : NonRoleSplitSource) :
    AlternativeNonRoleSourcePackage :=
  alternativeOfMinimalExactSourcePackage
    (NonRoleSplitSourceConstructionW26.w11ExactClosedChainPackageOfNonRoleSplitSource
      S)

def alternativeOfRemainderExactSourcePackage
    (R : RemainderExactSourcePackage) :
    AlternativeNonRoleSourcePackage where
  exposed :=
    PositiveExactChainAssemblyW27.exposedExactChainSourceOfPackage R.exact
  remainder := R
  remainder_exact_eq :=
    (PositiveExactChainAssemblyW27.package_minimalExactSource_left_inverse
      R.exact).symm

/-! ## Exact equivalences between the live source surfaces -/

theorem nonempty_alternative_iff_exposedExactChainSource :
    Nonempty AlternativeNonRoleSourcePackage <->
      Nonempty ExposedExactChainSource := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S => exact Nonempty.intro S.exposed
  case mpr =>
    intro h
    cases h with
    | intro S => exact Nonempty.intro (alternativeOfExposedExactChainSource S)

theorem nonempty_alternative_iff_positiveExactChainPackage :
    Nonempty AlternativeNonRoleSourcePackage <->
      Nonempty PositiveExactChainPackage := by
  exact Iff.trans nonempty_alternative_iff_exposedExactChainSource
    PositiveExactChainAssemblyW27.nonempty_package_iff_exposedExactChainSource.symm

theorem nonempty_alternative_iff_minimalExactSourcePackage :
    Nonempty AlternativeNonRoleSourcePackage <->
      Nonempty MinimalExactSourcePackage := by
  exact Iff.trans nonempty_alternative_iff_positiveExactChainPackage
    PositiveExactChainAssemblyW27.nonempty_package_iff_minimalExactSource

theorem nonempty_alternative_iff_nonRoleSplitSource :
    Nonempty AlternativeNonRoleSourcePackage <->
      Nonempty NonRoleSplitSource := by
  exact Iff.trans nonempty_alternative_iff_exposedExactChainSource
    PositiveExactChainAssemblyW27.nonempty_nonRoleSplitSource_iff_exposedExactChainSource.symm

theorem nonempty_alternative_iff_remainderExactSourcePackage :
    Nonempty AlternativeNonRoleSourcePackage <->
      Nonempty RemainderExactSourcePackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S => exact Nonempty.intro S.remainder
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro (alternativeOfRemainderExactSourcePackage R)

/-! ## Endpoint projections from source data -/

theorem exactTarget_of_alternative
    (S : AlternativeNonRoleSourcePackage) :
    ExactTarget :=
  PositiveExactChainPackageW26.exactTarget_of_package
    (positiveExactChainPackageOfAlternative S)

theorem arbitraryTarget_of_alternative
    (S : AlternativeNonRoleSourcePackage) :
    ArbitraryTarget :=
  RemainderExactSourceConstructionW27.arbitraryTarget_of_package S.remainder

theorem exactAndArbitraryTargets_of_alternative
    (S : AlternativeNonRoleSourcePackage) :
    ExactAndArbitraryTargets :=
  And.intro (exactTarget_of_alternative S)
    (arbitraryTarget_of_alternative S)

theorem exactAndArbitraryTargets_of_nonempty_alternative
    (H : Nonempty AlternativeNonRoleSourcePackage) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro S => exact exactAndArbitraryTargets_of_alternative S

theorem exactAndArbitraryTargets_iff_alternative :
    ExactAndArbitraryTargets <->
      Nonempty AlternativeNonRoleSourcePackage := by
  constructor
  case mp =>
    intro H
    exact
      nonempty_alternative_iff_positiveExactChainPackage.mpr
        (PositiveExactChainPackageW26.nonempty_package_iff_exactTarget.mpr
          H.1)
  case mpr =>
    exact exactAndArbitraryTargets_of_nonempty_alternative

/-! ## The honest remaining blocker for this route -/

theorem alternative_blocker_is_largeExactBlockTail_after_small_blocks :
    Nonempty AlternativeNonRoleSourcePackage <->
      ExactBlocksOneThroughFive /\ RemainingPositiveExactChainBlocker := by
  exact Iff.trans nonempty_alternative_iff_positiveExactChainPackage
    PositiveExactChainAssemblyW27.remainingBlocker_is_largeExactBlockTail_after_small_blocks

theorem not_nonempty_smallestConcreteSourceDependency :
    Not (Nonempty SmallestConcreteSourceDependency) :=
  PachTothW27FinalAssembly.not_nonempty_smallestConcreteSourceDependency

theorem not_nonempty_concreteLowerTableFamily :
    Not (Nonempty ConcreteNonConnectorLowerTableFamily) :=
  PachTothW27FinalAssembly.not_nonempty_concreteLowerTables

/-- The W28 route closes the endpoints from alternative source data while the
W27 concrete lower-table lane remains unavailable. -/
theorem alternativeRoute_avoids_concreteLowerTable_blocker :
    (Nonempty AlternativeNonRoleSourcePackage -> ExactAndArbitraryTargets) /\
      Not (Nonempty ConcreteNonConnectorLowerTableFamily) /\
        (Nonempty AlternativeNonRoleSourcePackage <->
          ExactBlocksOneThroughFive /\ RemainingPositiveExactChainBlocker) :=
  And.intro exactAndArbitraryTargets_of_nonempty_alternative
    (And.intro not_nonempty_concreteLowerTableFamily
      alternative_blocker_is_largeExactBlockTail_after_small_blocks)

end

end AlternativeNonRoleSourceW28
end PachToth

namespace Verified

abbrev PachTothW28AlternativeNonRoleSourcePackage : Type :=
  PachToth.AlternativeNonRoleSourceW28.AlternativeNonRoleSourcePackage

abbrev PachTothW28ExposedExactChainSource : Type :=
  PachToth.AlternativeNonRoleSourceW28.ExposedExactChainSource

abbrev PachTothW28RemainderExactSourcePackage : Type :=
  PachToth.AlternativeNonRoleSourceW28.RemainderExactSourcePackage

theorem pachtoth_w28_alternative_iff_exposedExactChainSource :
    Nonempty PachTothW28AlternativeNonRoleSourcePackage <->
      Nonempty PachTothW28ExposedExactChainSource :=
  PachToth.AlternativeNonRoleSourceW28.nonempty_alternative_iff_exposedExactChainSource

theorem pachtoth_w28_alternative_iff_remainderExactSourcePackage :
    Nonempty PachTothW28AlternativeNonRoleSourcePackage <->
      Nonempty PachTothW28RemainderExactSourcePackage :=
  PachToth.AlternativeNonRoleSourceW28.nonempty_alternative_iff_remainderExactSourcePackage

theorem pachtoth_w28_alternative_blocker_is_largeExactBlockTail_after_small_blocks :
    Nonempty PachTothW28AlternativeNonRoleSourcePackage <->
      PachToth.AlternativeNonRoleSourceW28.ExactBlocksOneThroughFive /\
        PachToth.AlternativeNonRoleSourceW28.RemainingPositiveExactChainBlocker :=
  PachToth.AlternativeNonRoleSourceW28.alternative_blocker_is_largeExactBlockTail_after_small_blocks

theorem pachtoth_w28_alternativeRoute_avoids_concreteLowerTable_blocker :
    (Nonempty PachTothW28AlternativeNonRoleSourcePackage ->
      PachToth.AlternativeNonRoleSourceW28.ExactAndArbitraryTargets) /\
      Not (Nonempty
        PachToth.AlternativeNonRoleSourceW28.ConcreteNonConnectorLowerTableFamily) /\
        (Nonempty PachTothW28AlternativeNonRoleSourcePackage <->
          PachToth.AlternativeNonRoleSourceW28.ExactBlocksOneThroughFive /\
            PachToth.AlternativeNonRoleSourceW28.RemainingPositiveExactChainBlocker) :=
  PachToth.AlternativeNonRoleSourceW28.alternativeRoute_avoids_concreteLowerTable_blocker

end Verified
end ErdosProblems1066
