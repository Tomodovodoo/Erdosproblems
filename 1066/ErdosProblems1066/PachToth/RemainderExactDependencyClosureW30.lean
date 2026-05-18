import ErdosProblems1066.PachToth.ExactChainFamilySourceW29
import ErdosProblems1066.PachToth.RemainderSplitClosureW29

set_option autoImplicit false

/-!
# W30 remainder/exact dependency closure

This leaf keeps the arbitrary-`n` remainder route source-facing.  The checked
finite remainders and translated split closure already build the W27/W28/W29
remainder packages once an exact-chain family source is supplied; no endpoint
target statement is used as source evidence.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RemainderExactDependencyClosureW30

noncomputable section

/-! ## Source and dependency vocabulary -/

abbrev ExactChainFamilySourcePackage : Type :=
  ExactChainFamilySourceW29.ExactChainFamilySourcePackage

abbrev ExactChainFamilySourceGate : Prop :=
  Nonempty ExactChainFamilySourcePackage

abbrev ExactChainFamily : Type :=
  RemainderSplitClosureW29.ExactChainFamily

abbrev RemainingExactChainFamilyDependency : Prop :=
  RemainderSplitClosureW29.RemainingExactChainFamilyDependency

abbrev ExactSourcePackage : Type :=
  RemainderSplitExactSourceW28.ExactSourcePackage

abbrev ExactSourcePackageGate : Prop :=
  Nonempty ExactSourcePackage

abbrev RemainingSplitBlocker : Prop :=
  RemainderSplitExactSourceW28.RemainingSplitBlocker

abbrev RemainderExactSourcePackage : Type :=
  RemainderExactSourceConstructionW27.RemainderExactSourcePackage

abbrev RemainderExactSourcePackageGate : Prop :=
  Nonempty RemainderExactSourcePackage

abbrev RemainderSplitExactSourcePackage : Type :=
  RemainderSplitClosureW29.RemainderSplitExactSourcePackage

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  Nonempty RemainderSplitExactSourcePackage

abbrev ArbitraryTarget : Prop :=
  RemainderSplitClosureW29.ArbitraryTarget

/-! ## Direct package constructors from the exact-chain family source -/

def exactChainFamilyOfSourcePackage
    (P : ExactChainFamilySourcePackage) :
    ExactChainFamily :=
  P.toExactChainFamily

def exactSourcePackageOfSourcePackage
    (P : ExactChainFamilySourcePackage) :
    ExactSourcePackage :=
  P.toPositiveExactChainPackage

def remainderExactSourcePackageOfSourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainderExactSourcePackage :=
  RemainderExactSourceConstructionW27.packageOfExactSource
    (exactSourcePackageOfSourcePackage P)

def remainderSplitExactSourcePackageOfSourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainderSplitExactSourcePackage :=
  RemainderSplitClosureW29.packageOfExactChainFamily
    (exactChainFamilyOfSourcePackage P)

@[simp]
theorem exactChainFamilyOfSourcePackage_eq
    (P : ExactChainFamilySourcePackage) :
    exactChainFamilyOfSourcePackage P = P.toExactChainFamily :=
  rfl

@[simp]
theorem exactSourcePackageOfSourcePackage_eq
    (P : ExactChainFamilySourcePackage) :
    exactSourcePackageOfSourcePackage P = P.toPositiveExactChainPackage :=
  rfl

/-! ## Remaining-dependency reductions -/

theorem remainingExactChainFamilyDependency_of_sourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainingExactChainFamilyDependency :=
  Nonempty.intro (exactChainFamilyOfSourcePackage P)

theorem exactChainFamilySourceGate_of_remainingExactChainFamilyDependency
    (H : RemainingExactChainFamilyDependency) :
    ExactChainFamilySourceGate := by
  cases H with
  | intro family =>
      exact
        Nonempty.intro
          (ExactChainFamilySourceW29.packageOfExactChainFamily family)

theorem remainingExactChainFamilyDependency_of_sourceGate
    (H : ExactChainFamilySourceGate) :
    RemainingExactChainFamilyDependency := by
  cases H with
  | intro P =>
      exact remainingExactChainFamilyDependency_of_sourcePackage P

theorem sourceGate_iff_remainingExactChainFamilyDependency :
    ExactChainFamilySourceGate <-> RemainingExactChainFamilyDependency := by
  constructor
  case mp =>
    exact remainingExactChainFamilyDependency_of_sourceGate
  case mpr =>
    exact exactChainFamilySourceGate_of_remainingExactChainFamilyDependency

theorem remainingExactChainFamilyDependency_iff_sourceGate :
    RemainingExactChainFamilyDependency <-> ExactChainFamilySourceGate :=
  sourceGate_iff_remainingExactChainFamilyDependency.symm

theorem exactSourcePackageGate_of_sourcePackage
    (P : ExactChainFamilySourcePackage) :
    ExactSourcePackageGate :=
  Nonempty.intro (exactSourcePackageOfSourcePackage P)

theorem exactChainFamilySourceGate_of_exactSourcePackageGate
    (H : ExactSourcePackageGate) :
    ExactChainFamilySourceGate := by
  cases H with
  | intro P =>
      exact
        Nonempty.intro
          (ExactChainFamilySourceW29.packageOfExactChainFamily P.exactChain)

theorem exactSourcePackageGate_of_sourceGate
    (H : ExactChainFamilySourceGate) :
    ExactSourcePackageGate := by
  cases H with
  | intro P =>
      exact exactSourcePackageGate_of_sourcePackage P

theorem sourceGate_iff_exactSourcePackageGate :
    ExactChainFamilySourceGate <-> ExactSourcePackageGate := by
  constructor
  case mp =>
    exact exactSourcePackageGate_of_sourceGate
  case mpr =>
    exact exactChainFamilySourceGate_of_exactSourcePackageGate

theorem exactSourcePackageGate_iff_sourceGate :
    ExactSourcePackageGate <-> ExactChainFamilySourceGate :=
  sourceGate_iff_exactSourcePackageGate.symm

theorem remainingSplitBlocker_of_sourceGate
    (H : ExactChainFamilySourceGate) :
    RemainingSplitBlocker :=
  exactSourcePackageGate_of_sourceGate H

theorem sourceGate_iff_remainingSplitBlocker :
    ExactChainFamilySourceGate <-> RemainingSplitBlocker :=
  sourceGate_iff_exactSourcePackageGate

theorem remainingSplitBlocker_iff_sourceGate :
    RemainingSplitBlocker <-> ExactChainFamilySourceGate :=
  sourceGate_iff_remainingSplitBlocker.symm

/-! ## Remainder package constructors from the same source -/

theorem remainderExactSourcePackageGate_of_sourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainderExactSourcePackageGate :=
  Nonempty.intro (remainderExactSourcePackageOfSourcePackage P)

theorem exactChainFamilySourceGate_of_remainderExactSourcePackageGate
    (H : RemainderExactSourcePackageGate) :
    ExactChainFamilySourceGate := by
  cases H with
  | intro S =>
      exact exactChainFamilySourceGate_of_exactSourcePackageGate
        (Nonempty.intro S.exact)

theorem remainderExactSourcePackageGate_of_sourceGate
    (H : ExactChainFamilySourceGate) :
    RemainderExactSourcePackageGate := by
  cases H with
  | intro P =>
      exact remainderExactSourcePackageGate_of_sourcePackage P

theorem sourceGate_iff_remainderExactSourcePackageGate :
    ExactChainFamilySourceGate <-> RemainderExactSourcePackageGate := by
  constructor
  case mp =>
    exact remainderExactSourcePackageGate_of_sourceGate
  case mpr =>
    exact exactChainFamilySourceGate_of_remainderExactSourcePackageGate

theorem remainderExactSourcePackageGate_iff_sourceGate :
    RemainderExactSourcePackageGate <-> ExactChainFamilySourceGate :=
  sourceGate_iff_remainderExactSourcePackageGate.symm

theorem remainderSplitExactSourcePackageGate_of_sourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainderSplitExactSourcePackageGate :=
  Nonempty.intro (remainderSplitExactSourcePackageOfSourcePackage P)

theorem remainderSplitExactSourcePackageGate_of_sourceGate
    (H : ExactChainFamilySourceGate) :
    RemainderSplitExactSourcePackageGate := by
  cases H with
  | intro P =>
      exact remainderSplitExactSourcePackageGate_of_sourcePackage P

theorem remainderSplitExactSourcePackageGate_of_remainingDependency
    (H : RemainingExactChainFamilyDependency) :
    RemainderSplitExactSourcePackageGate :=
  RemainderSplitClosureW29.nonempty_package_of_exactChainFamilyDependency H

theorem arbitraryTarget_of_sourcePackage
    (P : ExactChainFamilySourcePackage) :
    ArbitraryTarget :=
  RemainderSplitClosureW29.arbitraryTarget_of_exactChainFamily
    (exactChainFamilyOfSourcePackage P)

theorem arbitraryTarget_of_sourceGate
    (H : ExactChainFamilySourceGate) :
    ArbitraryTarget :=
  RemainderSplitClosureW29.arbitraryTarget_of_exactChainFamilyDependency
    (remainingExactChainFamilyDependency_of_sourceGate H)

/-! ## Compact W30 closure certificate -/

theorem dependencyClosure :
    (ExactChainFamilySourceGate <->
      RemainingExactChainFamilyDependency) /\
      (ExactChainFamilySourceGate <-> RemainingSplitBlocker) /\
        (ExactChainFamilySourceGate <->
          RemainderExactSourcePackageGate) /\
          (ExactChainFamilySourceGate ->
            RemainderSplitExactSourcePackageGate) /\
            (ExactChainFamilySourceGate -> ArbitraryTarget) :=
  And.intro sourceGate_iff_remainingExactChainFamilyDependency
    (And.intro sourceGate_iff_remainingSplitBlocker
      (And.intro sourceGate_iff_remainderExactSourcePackageGate
        (And.intro remainderSplitExactSourcePackageGate_of_sourceGate
          arbitraryTarget_of_sourceGate)))

end

end RemainderExactDependencyClosureW30
end PachToth

namespace Verified

abbrev PachTothW30ExactChainFamilySourceGate : Prop :=
  Nonempty PachToth.RemainderExactDependencyClosureW30.ExactChainFamilySourcePackage

abbrev PachTothW30RemainderRemainingExactChainFamilyDependency : Prop :=
  PachToth.RemainderExactDependencyClosureW30.RemainingExactChainFamilyDependency

abbrev PachTothW30RemainingSplitBlocker : Prop :=
  PachToth.RemainderExactDependencyClosureW30.RemainingSplitBlocker

abbrev PachTothW30RemainderExactSourcePackageGate : Prop :=
  PachToth.RemainderExactDependencyClosureW30.RemainderExactSourcePackageGate

abbrev PachTothW30RemainderSplitExactSourcePackageGate : Prop :=
  PachToth.RemainderExactDependencyClosureW30.RemainderSplitExactSourcePackageGate

theorem pachtoth_w30_sourceGate_iff_remainingExactChainFamilyDependency :
    PachTothW30ExactChainFamilySourceGate <->
      PachTothW30RemainderRemainingExactChainFamilyDependency :=
  PachToth.RemainderExactDependencyClosureW30.sourceGate_iff_remainingExactChainFamilyDependency

theorem pachtoth_w30_sourceGate_iff_remainingSplitBlocker :
    PachTothW30ExactChainFamilySourceGate <->
      PachTothW30RemainingSplitBlocker :=
  PachToth.RemainderExactDependencyClosureW30.sourceGate_iff_remainingSplitBlocker

theorem pachtoth_w30_sourceGate_iff_remainderExactSourcePackageGate :
    PachTothW30ExactChainFamilySourceGate <->
      PachTothW30RemainderExactSourcePackageGate :=
  PachToth.RemainderExactDependencyClosureW30.sourceGate_iff_remainderExactSourcePackageGate

theorem pachtoth_w30_remainderSplitExactSourcePackageGate_of_sourceGate
    (H : PachTothW30ExactChainFamilySourceGate) :
    PachTothW30RemainderSplitExactSourcePackageGate :=
  PachToth.RemainderExactDependencyClosureW30.remainderSplitExactSourcePackageGate_of_sourceGate
    H

theorem pachtoth_w30_arbitraryTarget_of_sourceGate
    (H : PachTothW30ExactChainFamilySourceGate) :
    PachToth.RemainderExactDependencyClosureW30.ArbitraryTarget :=
  PachToth.RemainderExactDependencyClosureW30.arbitraryTarget_of_sourceGate H

theorem pachtoth_w30_dependencyClosure :
    (PachTothW30ExactChainFamilySourceGate <->
      PachTothW30RemainderRemainingExactChainFamilyDependency) /\
      (PachTothW30ExactChainFamilySourceGate <->
        PachTothW30RemainingSplitBlocker) /\
        (PachTothW30ExactChainFamilySourceGate <->
          PachTothW30RemainderExactSourcePackageGate) /\
          (PachTothW30ExactChainFamilySourceGate ->
            PachTothW30RemainderSplitExactSourcePackageGate) /\
            (PachTothW30ExactChainFamilySourceGate ->
              PachToth.RemainderExactDependencyClosureW30.ArbitraryTarget) :=
  PachToth.RemainderExactDependencyClosureW30.dependencyClosure

end Verified
end ErdosProblems1066
