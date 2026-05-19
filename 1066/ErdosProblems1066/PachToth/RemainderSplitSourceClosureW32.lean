import ErdosProblems1066.PachToth.RemainderDependencyFinalW31
import ErdosProblems1066.PachToth.SmallLengthExactTargetsConcreteW24

set_option autoImplicit false

/-!
# W32 remainder split source closure

This leaf strengthens the W31 dependency package by exposing the exact
arbitrary-`n` split source data produced from an exact-chain family source:
the exact div/mod chain block, the checked finite remainder, the translated
remainder, the concrete separation certificate, and the canonical split
realization consumed by split soundness.

No endpoint target is used to manufacture source data.  The target fields
below are downstream consequences of the packaged W27/W28 split sources.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RemainderSplitSourceClosureW32

noncomputable section

/-! ## Source and split vocabulary -/

abbrev ExactChainFamilySourcePackage : Type :=
  RemainderDependencyFinalW31.ExactChainFamilySourcePackage

abbrev ExactChainFamilySourceGate : Prop :=
  RemainderDependencyFinalW31.ExactChainFamilySourceGate

abbrev RemainderExactDependencySource : Type :=
  RemainderDependencyFinalW31.RemainderExactDependencySource

abbrev RemainderExactDependencySourceGate : Prop :=
  Nonempty RemainderExactDependencySource

abbrev ExactChainFamily : Type :=
  RemainderDependencyFinalW31.ExactChainFamily

abbrev PositiveExactChainPackage : Type :=
  ExactChainFamilySourceW29.PositiveExactChainPackage

abbrev ExactClosedChainPackage : Type :=
  ExactChainFamilySourceW29.ExactClosedChainPackage

abbrev ClosedPlacementFamily : Type :=
  ExactChainFamilySourceW29.ClosedPlacementFamily

abbrev ClosedPlacementPackage : Type :=
  ExactChainFamilySourceW29.ClosedPlacementPackage

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  ExactChainFamilySourceW29.ExplicitClosedPlacementCertificateFamily

abbrev ExactBlocksOneThroughFive : Prop :=
  ExactChainFamilySourceW29.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  ExactChainFamilySourceW29.LargeExactBlockTargetsFromSix

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeTailExactSourceW28.LargeClosedPlacementFieldsFromSix

abbrev LargeTailExactSourcePackage : Type :=
  ExactChainFamilySourceW29.LargeTailExactSourcePackage

abbrev DeformedLengthOneExactBlocksTwoThroughFiveSource : Type :=
  SmallLengthExactTargetsConcreteW24.DeformedLengthOneExactBlocksTwoThroughFiveSource

abbrev MinimalExactRemainderSplitSourceBlocker : Prop :=
  ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix

abbrev ExactSourcePackage : Type :=
  RemainderDependencyFinalW31.ExactSourcePackage

abbrev RemainderExactSourcePackage : Type :=
  RemainderDependencyFinalW31.RemainderExactSourcePackage

abbrev RemainderSplitExactSourcePackage : Type :=
  RemainderDependencyFinalW31.RemainderSplitExactSourcePackage

abbrev RemainderExactSourcePackageGate : Prop :=
  RemainderDependencyFinalW31.RemainderExactSourcePackageGate

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  RemainderDependencyFinalW31.RemainderSplitExactSourcePackageGate

abbrev RemainingExactChainFamilyDependency : Prop :=
  RemainderDependencyFinalW31.RemainingExactChainFamilyDependency

abbrev RemainingSplitBlocker : Prop :=
  RemainderDependencyFinalW31.RemainingSplitBlocker

abbrev ExactChainUpper (k : Nat) : Type :=
  RemainderExactSourceConstructionW27.ExactChainUpper k

abbrev RemainderUpper (r : Nat) : Type :=
  RemainderExactSourceConstructionW27.RemainderUpper r

abbrev AppendedRemainderSeparation {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) : Prop :=
  RemainderExactSourceConstructionW27.AppendedRemainderSeparation
    chain remainder

abbrev FarApartRemainderCertificate {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) : Type :=
  RemainderExactSourceConstructionW27.FarApartRemainderCertificate
    chain remainder

abbrev CanonicalSplitRealization (k r : Nat) : Type :=
  RemainderExactSourceConstructionW27.CanonicalSplitRealization k r

abbrev ExistsCanonicalSplitRealization (k r : Nat) : Prop :=
  SplitCertificateBridge.exists_canonicalSplitRealization k r

abbrev RemainderExactSourceAt
    (P : ExactSourcePackage) (n : Nat) : Type :=
  RemainderExactSourceConstructionW27.RemainderExactSourceAt P n

abbrev SplitExactSourceAt (k r : Nat) : Type :=
  RemainderSplitExactSourceW28.SplitExactSourceAt k r

abbrev DivModSplitExactSource (n : Nat) : Type :=
  RemainderSplitExactSourceW28.DivModSplitExactSource n

abbrev FixedTarget (n : Nat) : Prop :=
  RemainderExactSourceConstructionW27.FixedTarget n

abbrev ArbitraryTarget : Prop :=
  RemainderDependencyFinalW31.ArbitraryTarget

/-! ## Pointwise arbitrary-`n` source package -/

/--
For one vertex count `n`, this record keeps both downstream source views:
the W27 exact/remainder construction data and the W28 div/mod split source.
The target proofs are consequences of those records and their checked
canonical split realizations.
-/
structure ExactRemainderSplitSourceAt
    (P : ExactChainFamilySourcePackage) (n : Nat) where
  remainderExactAt :
    RemainderExactSourceAt
      (RemainderExactDependencyClosureW30.exactSourcePackageOfSourcePackage P)
      n
  splitDivMod : DivModSplitExactSource n
  splitSourceAt : SplitExactSourceAt (n / 16) (n % 16)
  splitSourceAt_eq : splitSourceAt = splitDivMod.source
  exactChain : ExactChainUpper (n / 16)
  exactChain_eq : exactChain = remainderExactAt.chain
  checkedRemainder : RemainderUpper (n % 16)
  checkedRemainder_eq : checkedRemainder = remainderExactAt.remainder
  translatedRemainder : RemainderUpper (n % 16)
  translatedRemainder_eq :
    translatedRemainder = remainderExactAt.translatedRemainder
  separation :
    AppendedRemainderSeparation
      exactChain.config
      translatedRemainder.config
  farApart :
    FarApartRemainderCertificate
      exactChain.config
      translatedRemainder.config
  realization : CanonicalSplitRealization (n / 16) (n % 16)
  realization_eq : realization = remainderExactAt.realization
  fixedTarget_from_remainderExact : FixedTarget n
  fixedTarget_from_splitSource : FixedTarget n

def sourceAtOfExactChainSourcePackage
    (P : ExactChainFamilySourcePackage) (n : Nat) :
    ExactRemainderSplitSourceAt P n :=
  let R :=
    (RemainderExactDependencyClosureW30.remainderExactSourcePackageOfSourcePackage
      P).source n
  let D :=
    (RemainderExactDependencyClosureW30.remainderSplitExactSourcePackageOfSourcePackage
      P).sourceAt n
  { remainderExactAt := R
    splitDivMod := D
    splitSourceAt := D.source
    splitSourceAt_eq := rfl
    exactChain := R.chain
    exactChain_eq := rfl
    checkedRemainder := R.remainder
    checkedRemainder_eq := rfl
    translatedRemainder := R.translatedRemainder
    translatedRemainder_eq := rfl
    separation := R.separation
    farApart := R.farApart
    realization := R.realization
    realization_eq := rfl
    fixedTarget_from_remainderExact :=
      RemainderExactSourceConstructionW27.fixedTarget_of_sourceAt R
    fixedTarget_from_splitSource :=
      RemainderSplitExactSourceW28.fixedTarget_of_divModSource D }

theorem fixedTarget_of_sourceAt
    {P : ExactChainFamilySourcePackage} {n : Nat}
    (S : ExactRemainderSplitSourceAt P n) :
    FixedTarget n :=
  S.fixedTarget_from_remainderExact

theorem splitFixedTarget_of_sourceAt
    {P : ExactChainFamilySourcePackage} {n : Nat}
    (S : ExactRemainderSplitSourceAt P n) :
    FixedTarget n :=
  S.fixedTarget_from_splitSource

theorem exists_canonicalSplitRealization_of_splitSourceAt
    {k r : Nat} (S : SplitExactSourceAt k r) :
    ExistsCanonicalSplitRealization k r :=
  RemainderSplitExactSourceW28.exists_canonicalSplitRealization_of_sourceAt S

theorem exists_canonicalSplitRealization_of_exactChain_farApart
    {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r)
    (F : FarApartRemainderCertificate chain.config remainder.config) :
    ExistsCanonicalSplitRealization k r :=
  SplitCertificateBridge.exists_canonicalSplitRealization_of_exactChain_farApart
    chain remainder F

theorem exists_canonicalSplitRealization_of_realization
    {k r : Nat} (S : CanonicalSplitRealization k r) :
    ExistsCanonicalSplitRealization k r := by
  exact Exists.intro S True.intro

theorem exists_canonicalSplitRealization_of_sourceAt_farApart
    {P : ExactChainFamilySourcePackage} {n : Nat}
    (S : ExactRemainderSplitSourceAt P n) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  exists_canonicalSplitRealization_of_exactChain_farApart
    S.exactChain S.translatedRemainder S.farApart

theorem exists_canonicalSplitRealization_of_sourceAt
    {P : ExactChainFamilySourcePackage} {n : Nat}
    (S : ExactRemainderSplitSourceAt P n) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  exists_canonicalSplitRealization_of_sourceAt_farApart S

theorem exists_canonicalSplitRealization_of_sourceAt_realization
    {P : ExactChainFamilySourcePackage} {n : Nat}
    (S : ExactRemainderSplitSourceAt P n) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  exists_canonicalSplitRealization_of_realization S.realization

/-! ## Full source closure package -/

/--
The W32 package is the W31 exact-chain source together with all exact,
remainder, and split-source products derived from it.
-/
structure ExactRemainderSplitSourcePackage where
  exactChainSource : ExactChainFamilySourcePackage
  w31Source : RemainderExactDependencySource
  w31Source_eq :
    w31Source =
      RemainderDependencyFinalW31.sourceOfExactChainSourcePackage
        exactChainSource
  exactChainFamily : ExactChainFamily
  exactChainFamily_eq :
    exactChainFamily =
      RemainderExactDependencyClosureW30.exactChainFamilyOfSourcePackage
        exactChainSource
  exactSource : ExactSourcePackage
  exactSource_eq :
    exactSource =
      RemainderExactDependencyClosureW30.exactSourcePackageOfSourcePackage
        exactChainSource
  remainderExactSource : RemainderExactSourcePackage
  remainderExactSource_eq :
    remainderExactSource =
      RemainderExactDependencyClosureW30.remainderExactSourcePackageOfSourcePackage
        exactChainSource
  remainderSplitExactSource : RemainderSplitExactSourcePackage
  remainderSplitExactSource_eq :
    remainderSplitExactSource =
      RemainderExactDependencyClosureW30.remainderSplitExactSourcePackageOfSourcePackage
        exactChainSource
  sourceAt : forall n : Nat,
    ExactRemainderSplitSourceAt exactChainSource n
  fixedTarget : forall n : Nat, FixedTarget n
  arbitraryTarget : ArbitraryTarget
  exactChainDependency : RemainingExactChainFamilyDependency
  splitBlocker : RemainingSplitBlocker

abbrev ExactRemainderSplitSourcePackageGate : Prop :=
  Nonempty ExactRemainderSplitSourcePackage

def packageOfExactChainSourcePackage
    (P : ExactChainFamilySourcePackage) :
    ExactRemainderSplitSourcePackage where
  exactChainSource := P
  w31Source :=
    RemainderDependencyFinalW31.sourceOfExactChainSourcePackage P
  w31Source_eq := rfl
  exactChainFamily :=
    RemainderExactDependencyClosureW30.exactChainFamilyOfSourcePackage P
  exactChainFamily_eq := rfl
  exactSource :=
    RemainderExactDependencyClosureW30.exactSourcePackageOfSourcePackage P
  exactSource_eq := rfl
  remainderExactSource :=
    RemainderExactDependencyClosureW30.remainderExactSourcePackageOfSourcePackage
      P
  remainderExactSource_eq := rfl
  remainderSplitExactSource :=
    RemainderExactDependencyClosureW30.remainderSplitExactSourcePackageOfSourcePackage
      P
  remainderSplitExactSource_eq := rfl
  sourceAt := sourceAtOfExactChainSourcePackage P
  fixedTarget := fun n =>
    RemainderExactSourceConstructionW27.fixedTarget_of_package
      (RemainderExactDependencyClosureW30.remainderExactSourcePackageOfSourcePackage
        P)
      n
  arbitraryTarget :=
    RemainderExactDependencyClosureW30.arbitraryTarget_of_sourcePackage P
  exactChainDependency :=
    RemainderExactDependencyClosureW30.remainingExactChainFamilyDependency_of_sourcePackage
      P
  splitBlocker :=
    RemainderExactDependencyClosureW30.remainingSplitBlocker_of_sourceGate
      (Nonempty.intro P)

def packageOfW31Source
    (S : RemainderExactDependencySource) :
    ExactRemainderSplitSourcePackage :=
  packageOfExactChainSourcePackage S.exactChainSource

theorem fixedTarget_of_package
    (S : ExactRemainderSplitSourcePackage) (n : Nat) :
    FixedTarget n :=
  S.fixedTarget n

theorem arbitraryTarget_of_package
    (S : ExactRemainderSplitSourcePackage) :
    ArbitraryTarget :=
  S.arbitraryTarget

theorem exists_canonicalSplitRealization_of_package
    (S : ExactRemainderSplitSourcePackage) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  exists_canonicalSplitRealization_of_sourceAt (S.sourceAt n)

theorem remainderExactSourcePackageGate_of_package
    (S : ExactRemainderSplitSourcePackage) :
    RemainderExactSourcePackageGate :=
  Nonempty.intro S.remainderExactSource

theorem remainderSplitExactSourcePackageGate_of_package
    (S : ExactRemainderSplitSourcePackage) :
    RemainderSplitExactSourcePackageGate :=
  Nonempty.intro S.remainderSplitExactSource

/-! ## Source gates and closure certificate -/

theorem packageGate_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    ExactRemainderSplitSourcePackageGate := by
  cases H with
  | intro P =>
      exact Nonempty.intro (packageOfExactChainSourcePackage P)

theorem exactChainFamilySourceGate_of_packageGate
    (H : ExactRemainderSplitSourcePackageGate) :
    ExactChainFamilySourceGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.exactChainSource

theorem packageGate_iff_exactChainFamilySourceGate :
    ExactRemainderSplitSourcePackageGate <->
      ExactChainFamilySourceGate := by
  constructor
  case mp =>
    exact exactChainFamilySourceGate_of_packageGate
  case mpr =>
    exact packageGate_of_exactChainFamilySourceGate

theorem packageGate_of_exactChainFamily
    (H : ExactChainFamily) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_exactChainFamilySourceGate
    (Nonempty.intro (ExactChainFamilySourceW29.packageOfExactChainFamily H))

theorem packageGate_of_positiveExactChainPackage
    (P : PositiveExactChainPackage) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_exactChainFamilySourceGate
    (Nonempty.intro
      (ExactChainFamilySourceW29.packageOfPositiveExactChainPackage P))

theorem packageGate_of_positiveExactChainPackageGate
    (H : Nonempty PositiveExactChainPackage) :
    ExactRemainderSplitSourcePackageGate := by
  cases H with
  | intro P =>
      exact packageGate_of_positiveExactChainPackage P

theorem packageGate_of_exactClosedChainPackage
    (P : ExactClosedChainPackage) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_exactChainFamilySourceGate
    (Nonempty.intro
      (ExactChainFamilySourceW29.packageOfExactClosedChainPackage P))

theorem packageGate_of_exactClosedChainPackageGate
    (H : Nonempty ExactClosedChainPackage) :
    ExactRemainderSplitSourcePackageGate := by
  cases H with
  | intro P =>
      exact packageGate_of_exactClosedChainPackage P

theorem packageGate_of_closedPlacementFamily
    (H : ClosedPlacementFamily) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_exactChainFamilySourceGate
    (Nonempty.intro
      (ExactChainFamilySourceW29.packageOfClosedPlacementFamily H))

theorem packageGate_of_closedPlacementFamilyGate
    (H : Nonempty ClosedPlacementFamily) :
    ExactRemainderSplitSourcePackageGate := by
  cases H with
  | intro F =>
      exact packageGate_of_closedPlacementFamily F

theorem packageGate_of_closedPlacementPackage
    (P : ClosedPlacementPackage) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_exactChainFamilySourceGate
    (Nonempty.intro
      (ExactChainFamilySourceW29.packageOfClosedPlacementPackage P))

theorem packageGate_of_closedPlacementPackageGate
    (H : Nonempty ClosedPlacementPackage) :
    ExactRemainderSplitSourcePackageGate := by
  cases H with
  | intro P =>
      exact packageGate_of_closedPlacementPackage P

theorem packageGate_of_explicitClosedPlacementCertificateFamily
    (H : ExplicitClosedPlacementCertificateFamily) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_exactChainFamilySourceGate
    (Nonempty.intro
      (ExactChainFamilySourceW29.packageOfExplicitClosedPlacementCertificateFamily
        H))

theorem packageGate_of_explicitClosedPlacementCertificateFamilyGate
    (H : Nonempty ExplicitClosedPlacementCertificateFamily) :
    ExactRemainderSplitSourcePackageGate := by
  cases H with
  | intro F =>
      exact packageGate_of_explicitClosedPlacementCertificateFamily F

theorem largeExactBlockTargetsFromSix_of_largeTailSourcePackage
    (large : LargeTailExactSourcePackage) :
    LargeExactBlockTargetsFromSix :=
  LargeTailExactSourceW28.remainingBlocker_of_largeTailExactSourcePackage
    large

theorem largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsFromSix
    (large : LargeClosedPlacementFieldsFromSix) :
    LargeExactBlockTargetsFromSix :=
  LargeTailExactSourceW28.remainingBlocker_of_largeClosedPlacementFieldsFromSix
    large

theorem packageGate_of_smallBlocks_and_largeTail
    (small : ExactBlocksOneThroughFive)
    (large : LargeExactBlockTargetsFromSix) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_exactChainFamilySourceGate
    (Nonempty.intro
      (ExactChainFamilySourceW29.packageOfSmallBlocksAndLargeTail small large))

theorem packageGate_of_deformedSmallSource_and_largeTail
    (small : DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (large : LargeExactBlockTargetsFromSix) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_smallBlocks_and_largeTail
    small.exactBlocksOneThroughFive large

theorem packageGate_of_deformedSmallSourceGate_and_largeTail
    (Hsmall : Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (large : LargeExactBlockTargetsFromSix) :
    ExactRemainderSplitSourcePackageGate := by
  cases Hsmall with
  | intro small =>
      exact packageGate_of_deformedSmallSource_and_largeTail small large

theorem minimalBlocker_of_deformedSmallSource_and_largeTail
    (small : DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (large : LargeExactBlockTargetsFromSix) :
    MinimalExactRemainderSplitSourceBlocker :=
  And.intro small.exactBlocksOneThroughFive large

theorem minimalBlocker_of_smallBlocks_and_largeClosedPlacementFieldsFromSix
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    MinimalExactRemainderSplitSourceBlocker :=
  And.intro small
    (largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsFromSix
      large)

theorem packageGate_of_smallBlocks_and_largeClosedPlacementFieldsFromSix
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_smallBlocks_and_largeTail small
    (largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsFromSix
      large)

theorem packageGate_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
    (small : DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_smallBlocks_and_largeClosedPlacementFieldsFromSix
    small.exactBlocksOneThroughFive large

theorem packageGate_of_deformedSmallSourceGate_and_largeClosedPlacementFieldsFromSixGate
    (Hsmall : Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (Hlarge : Nonempty LargeClosedPlacementFieldsFromSix) :
    ExactRemainderSplitSourcePackageGate := by
  cases Hsmall with
  | intro small =>
      cases Hlarge with
      | intro large =>
          exact
            packageGate_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
              small large

theorem minimalBlocker_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
    (small : DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (large : LargeClosedPlacementFieldsFromSix) :
    MinimalExactRemainderSplitSourceBlocker :=
  minimalBlocker_of_smallBlocks_and_largeClosedPlacementFieldsFromSix
    small.exactBlocksOneThroughFive large

theorem minimalBlocker_of_deformedSmallSourceGate_and_largeClosedPlacementFieldsFromSixGate
    (Hsmall : Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (Hlarge : Nonempty LargeClosedPlacementFieldsFromSix) :
    MinimalExactRemainderSplitSourceBlocker := by
  cases Hsmall with
  | intro small =>
      cases Hlarge with
      | intro large =>
          exact
            minimalBlocker_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
              small large

theorem packageGate_of_largeTailSource_and_smallBlocks
    (large : LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_of_exactChainFamilySourceGate
    (Nonempty.intro
      (ExactChainFamilySourceW29.packageOfLargeTailExactSourcePackage
        large small))

theorem packageGate_of_largeTailSourceGate_and_smallBlocks
    (Hlarge : Nonempty LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    ExactRemainderSplitSourcePackageGate := by
  cases Hlarge with
  | intro large =>
      exact packageGate_of_largeTailSource_and_smallBlocks large small

theorem exactChainFamilySourceGate_iff_minimalBlocker :
    ExactChainFamilySourceGate <->
      MinimalExactRemainderSplitSourceBlocker :=
  ExactChainFamilySourceW29.nonempty_package_iff_smallBlocks_and_largeTail

theorem packageGate_iff_minimalBlocker :
    ExactRemainderSplitSourcePackageGate <->
      MinimalExactRemainderSplitSourceBlocker :=
  Iff.trans packageGate_iff_exactChainFamilySourceGate
    exactChainFamilySourceGate_iff_minimalBlocker

theorem minimalBlocker_of_packageGate
    (H : ExactRemainderSplitSourcePackageGate) :
    MinimalExactRemainderSplitSourceBlocker :=
  packageGate_iff_minimalBlocker.mp H

theorem packageGate_of_minimalBlocker
    (H : MinimalExactRemainderSplitSourceBlocker) :
    ExactRemainderSplitSourcePackageGate :=
  packageGate_iff_minimalBlocker.mpr H

theorem packageGate_of_w31SourceGate
    (H : RemainderExactDependencySourceGate) :
    ExactRemainderSplitSourcePackageGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro (packageOfW31Source S)

theorem w31SourceGate_of_packageGate
    (H : ExactRemainderSplitSourcePackageGate) :
    RemainderExactDependencySourceGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.w31Source

theorem remainderExactSourcePackageGate_of_packageGate
    (H : ExactRemainderSplitSourcePackageGate) :
    RemainderExactSourcePackageGate := by
  cases H with
  | intro S =>
      exact remainderExactSourcePackageGate_of_package S

theorem remainderSplitExactSourcePackageGate_of_packageGate
    (H : ExactRemainderSplitSourcePackageGate) :
    RemainderSplitExactSourcePackageGate := by
  cases H with
  | intro S =>
      exact remainderSplitExactSourcePackageGate_of_package S

theorem arbitraryTarget_of_packageGate
    (H : ExactRemainderSplitSourcePackageGate) :
    ArbitraryTarget := by
  cases H with
  | intro S =>
      exact arbitraryTarget_of_package S

theorem exists_canonicalSplitRealization_of_packageGate
    (H : ExactRemainderSplitSourcePackageGate) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) := by
  cases H with
  | intro S =>
      exact exists_canonicalSplitRealization_of_package S n

theorem arbitraryTarget_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    ArbitraryTarget :=
  arbitraryTarget_of_packageGate
    (packageGate_of_exactChainFamilySourceGate H)

theorem exists_canonicalSplitRealization_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  exists_canonicalSplitRealization_of_packageGate
    (packageGate_of_exactChainFamilySourceGate H) n

theorem exists_canonicalSplitRealization_of_closedPlacementFamilyGate
    (H : Nonempty ClosedPlacementFamily) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  exists_canonicalSplitRealization_of_packageGate
    (packageGate_of_closedPlacementFamilyGate H) n

structure RemainderSplitSourceClosureCertificate : Prop where
  package_iff_sourceGate :
    ExactRemainderSplitSourcePackageGate <->
      ExactChainFamilySourceGate
  package_iff_minimalBlocker :
    ExactRemainderSplitSourcePackageGate <->
      MinimalExactRemainderSplitSourceBlocker
  exactChainFamilyFeedsPackage :
    ExactChainFamily -> ExactRemainderSplitSourcePackageGate
  positiveExactChainPackageFeedsPackage :
    Nonempty PositiveExactChainPackage ->
      ExactRemainderSplitSourcePackageGate
  exactClosedChainPackageFeedsPackage :
    Nonempty ExactClosedChainPackage ->
      ExactRemainderSplitSourcePackageGate
  closedPlacementFamilyFeedsPackage :
    Nonempty ClosedPlacementFamily ->
      ExactRemainderSplitSourcePackageGate
  closedPlacementPackageFeedsPackage :
    Nonempty ClosedPlacementPackage ->
      ExactRemainderSplitSourcePackageGate
  explicitClosedPlacementFeedsPackage :
    Nonempty ExplicitClosedPlacementCertificateFamily ->
      ExactRemainderSplitSourcePackageGate
  largeTailSourceFeedsLargeExactTail :
    LargeTailExactSourcePackage -> LargeExactBlockTargetsFromSix
  largeClosedPlacementFieldsFeedLargeExactTail :
    LargeClosedPlacementFieldsFromSix -> LargeExactBlockTargetsFromSix
  minimalBlockerFeedsPackage :
    MinimalExactRemainderSplitSourceBlocker ->
      ExactRemainderSplitSourcePackageGate
  smallBlocksAndLargeClosedPlacementFieldsFeedMinimalBlocker :
    ExactBlocksOneThroughFive ->
      LargeClosedPlacementFieldsFromSix ->
        MinimalExactRemainderSplitSourceBlocker
  smallBlocksAndLargeClosedPlacementFieldsFeedPackage :
    ExactBlocksOneThroughFive ->
      LargeClosedPlacementFieldsFromSix ->
        ExactRemainderSplitSourcePackageGate
  deformedSmallSourceAndLargeTailFeedsPackage :
    DeformedLengthOneExactBlocksTwoThroughFiveSource ->
      LargeExactBlockTargetsFromSix ->
        ExactRemainderSplitSourcePackageGate
  deformedSmallSourceAndLargeClosedPlacementFieldsFeedsPackage :
    DeformedLengthOneExactBlocksTwoThroughFiveSource ->
      LargeClosedPlacementFieldsFromSix ->
        ExactRemainderSplitSourcePackageGate
  deformedSmallSourceAndLargeTailFeedsMinimalBlocker :
    DeformedLengthOneExactBlocksTwoThroughFiveSource ->
      LargeExactBlockTargetsFromSix ->
        MinimalExactRemainderSplitSourceBlocker
  deformedSmallSourceAndLargeClosedPlacementFieldsFeedsMinimalBlocker :
    DeformedLengthOneExactBlocksTwoThroughFiveSource ->
      LargeClosedPlacementFieldsFromSix ->
        MinimalExactRemainderSplitSourceBlocker
  packageFeedsMinimalBlocker :
    ExactRemainderSplitSourcePackageGate ->
      MinimalExactRemainderSplitSourceBlocker
  w31SourceGateFeedsPackage :
    RemainderExactDependencySourceGate ->
      ExactRemainderSplitSourcePackageGate
  packageFeedsW31SourceGate :
    ExactRemainderSplitSourcePackageGate ->
      RemainderExactDependencySourceGate
  packageFeedsRemainderExact :
    ExactRemainderSplitSourcePackageGate ->
      RemainderExactSourcePackageGate
  packageFeedsRemainderSplit :
    ExactRemainderSplitSourcePackageGate ->
      RemainderSplitExactSourcePackageGate
  packageFeedsArbitraryTarget :
    ExactRemainderSplitSourcePackageGate ->
      ArbitraryTarget
  sourceAtFeedsCanonicalSplit :
    forall (P : ExactChainFamilySourcePackage) (n : Nat),
      ExactRemainderSplitSourceAt P n ->
        ExistsCanonicalSplitRealization (n / 16) (n % 16)
  packageFeedsCanonicalSplit :
    ExactRemainderSplitSourcePackageGate ->
      forall n : Nat,
        ExistsCanonicalSplitRealization (n / 16) (n % 16)
  sourceGateFeedsCanonicalSplit :
    ExactChainFamilySourceGate ->
      forall n : Nat,
        ExistsCanonicalSplitRealization (n / 16) (n % 16)
  closedPlacementFamilyFeedsCanonicalSplit :
    Nonempty ClosedPlacementFamily ->
      forall n : Nat,
        ExistsCanonicalSplitRealization (n / 16) (n % 16)
  sourceGateFeedsArbitraryTarget :
    ExactChainFamilySourceGate ->
      ArbitraryTarget

theorem remainderSplitSourceClosureCertificate :
    RemainderSplitSourceClosureCertificate where
  package_iff_sourceGate :=
    packageGate_iff_exactChainFamilySourceGate
  package_iff_minimalBlocker :=
    packageGate_iff_minimalBlocker
  exactChainFamilyFeedsPackage :=
    packageGate_of_exactChainFamily
  positiveExactChainPackageFeedsPackage :=
    packageGate_of_positiveExactChainPackageGate
  exactClosedChainPackageFeedsPackage :=
    packageGate_of_exactClosedChainPackageGate
  closedPlacementFamilyFeedsPackage :=
    packageGate_of_closedPlacementFamilyGate
  closedPlacementPackageFeedsPackage :=
    packageGate_of_closedPlacementPackageGate
  explicitClosedPlacementFeedsPackage :=
    packageGate_of_explicitClosedPlacementCertificateFamilyGate
  largeTailSourceFeedsLargeExactTail :=
    largeExactBlockTargetsFromSix_of_largeTailSourcePackage
  largeClosedPlacementFieldsFeedLargeExactTail :=
    largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsFromSix
  minimalBlockerFeedsPackage :=
    packageGate_of_minimalBlocker
  smallBlocksAndLargeClosedPlacementFieldsFeedMinimalBlocker :=
    minimalBlocker_of_smallBlocks_and_largeClosedPlacementFieldsFromSix
  smallBlocksAndLargeClosedPlacementFieldsFeedPackage :=
    packageGate_of_smallBlocks_and_largeClosedPlacementFieldsFromSix
  deformedSmallSourceAndLargeTailFeedsPackage :=
    packageGate_of_deformedSmallSource_and_largeTail
  deformedSmallSourceAndLargeClosedPlacementFieldsFeedsPackage :=
    packageGate_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
  deformedSmallSourceAndLargeTailFeedsMinimalBlocker :=
    minimalBlocker_of_deformedSmallSource_and_largeTail
  deformedSmallSourceAndLargeClosedPlacementFieldsFeedsMinimalBlocker :=
    minimalBlocker_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
  packageFeedsMinimalBlocker :=
    minimalBlocker_of_packageGate
  w31SourceGateFeedsPackage :=
    packageGate_of_w31SourceGate
  packageFeedsW31SourceGate :=
    w31SourceGate_of_packageGate
  packageFeedsRemainderExact :=
    remainderExactSourcePackageGate_of_packageGate
  packageFeedsRemainderSplit :=
    remainderSplitExactSourcePackageGate_of_packageGate
  packageFeedsArbitraryTarget :=
    arbitraryTarget_of_packageGate
  sourceAtFeedsCanonicalSplit := by
    intro _P _n S
    exact exists_canonicalSplitRealization_of_sourceAt S
  packageFeedsCanonicalSplit :=
    exists_canonicalSplitRealization_of_packageGate
  sourceGateFeedsCanonicalSplit :=
    exists_canonicalSplitRealization_of_exactChainFamilySourceGate
  closedPlacementFamilyFeedsCanonicalSplit :=
    exists_canonicalSplitRealization_of_closedPlacementFamilyGate
  sourceGateFeedsArbitraryTarget :=
    arbitraryTarget_of_exactChainFamilySourceGate

end

end RemainderSplitSourceClosureW32
end PachToth
end ErdosProblems1066
