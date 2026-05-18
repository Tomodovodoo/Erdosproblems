import ErdosProblems1066.PachToth.RemainderExactDependencyClosureW30

set_option autoImplicit false

/-!
# W31 remainder dependency final layer

This file is the W31 source-facing closure for the remainder route.  The
finite remainder configurations and split certificates are inherited from the
W27-W30 construction chain; the only remaining input is exact-chain source
data.  No endpoint target statement is used to manufacture source data.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RemainderDependencyFinalW31

noncomputable section

/-! ## Source and dependency vocabulary -/

abbrev ExactChainFamilySourcePackage : Type :=
  RemainderExactDependencyClosureW30.ExactChainFamilySourcePackage

abbrev ExactChainFamilySourceGate : Prop :=
  Nonempty ExactChainFamilySourcePackage

abbrev ExactChainFamily : Type :=
  RemainderExactDependencyClosureW30.ExactChainFamily

abbrev ExactSourcePackage : Type :=
  RemainderExactDependencyClosureW30.ExactSourcePackage

abbrev RemainderExactSourcePackage : Type :=
  RemainderExactDependencyClosureW30.RemainderExactSourcePackage

abbrev RemainderSplitExactSourcePackage : Type :=
  RemainderExactDependencyClosureW30.RemainderSplitExactSourcePackage

abbrev RemainingExactChainFamilyDependency : Prop :=
  RemainderExactDependencyClosureW30.RemainingExactChainFamilyDependency

abbrev RemainingSplitBlocker : Prop :=
  RemainderExactDependencyClosureW30.RemainingSplitBlocker

abbrev RemainderExactSourcePackageGate : Prop :=
  RemainderExactDependencyClosureW30.RemainderExactSourcePackageGate

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  RemainderExactDependencyClosureW30.RemainderSplitExactSourcePackageGate

abbrev ArbitraryTarget : Prop :=
  RemainderExactDependencyClosureW30.ArbitraryTarget

/-!
The precise W31 blocker is the exact-chain source gate.  Once this source
package is present, the checked finite remainders and split certificates are
constructed by the inherited W27-W30 chain.
-/
abbrev RemainingExactChainDependencyBlocker : Prop :=
  ExactChainFamilySourceGate

/-! ## Constructed W31 source bundle -/

structure RemainderExactDependencySource where
  exactChainSource : ExactChainFamilySourcePackage
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
  exactChainDependency : RemainingExactChainFamilyDependency
  splitBlocker : RemainingSplitBlocker

def sourceOfExactChainSourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainderExactDependencySource where
  exactChainSource := P
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
  exactChainDependency :=
    RemainderExactDependencyClosureW30.remainingExactChainFamilyDependency_of_sourcePackage
      P
  splitBlocker :=
    RemainderExactDependencyClosureW30.remainingSplitBlocker_of_sourceGate
      (Nonempty.intro P)

theorem nonempty_source_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    Nonempty RemainderExactDependencySource := by
  cases H with
  | intro P =>
      exact Nonempty.intro (sourceOfExactChainSourcePackage P)

theorem exactChainDependency_of_source
    (S : RemainderExactDependencySource) :
    RemainingExactChainFamilyDependency :=
  S.exactChainDependency

theorem splitBlocker_of_source
    (S : RemainderExactDependencySource) :
    RemainingSplitBlocker :=
  S.splitBlocker

/-! ## Final source-to-remainder closures -/

theorem remainingExactChainFamilyDependency_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    RemainingExactChainFamilyDependency :=
  RemainderExactDependencyClosureW30.remainingExactChainFamilyDependency_of_sourceGate
    H

theorem remainderExactSourcePackageGate_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    RemainderExactSourcePackageGate :=
  RemainderExactDependencyClosureW30.remainderExactSourcePackageGate_of_sourceGate
    H

theorem remainderSplitExactSourcePackageGate_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    RemainderSplitExactSourcePackageGate :=
  RemainderExactDependencyClosureW30.remainderSplitExactSourcePackageGate_of_sourceGate
    H

theorem arbitraryTarget_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    ArbitraryTarget :=
  RemainderExactDependencyClosureW30.arbitraryTarget_of_sourceGate H

theorem checkedBlocker_is_exactChainFamilySourceGate :
    RemainingExactChainDependencyBlocker <-> ExactChainFamilySourceGate :=
  Iff.rfl

theorem dependencyClosureFinal :
    (ExactChainFamilySourceGate ->
      Nonempty RemainderExactDependencySource) /\
      (ExactChainFamilySourceGate ->
        RemainingExactChainFamilyDependency) /\
        (ExactChainFamilySourceGate ->
          RemainderExactSourcePackageGate) /\
          (ExactChainFamilySourceGate ->
            RemainderSplitExactSourcePackageGate) /\
            (RemainingExactChainDependencyBlocker <->
              ExactChainFamilySourceGate) /\
              (ExactChainFamilySourceGate -> ArbitraryTarget) :=
  And.intro nonempty_source_of_exactChainFamilySourceGate
    (And.intro remainingExactChainFamilyDependency_of_exactChainFamilySourceGate
      (And.intro remainderExactSourcePackageGate_of_exactChainFamilySourceGate
        (And.intro remainderSplitExactSourcePackageGate_of_exactChainFamilySourceGate
          (And.intro checkedBlocker_is_exactChainFamilySourceGate
            arbitraryTarget_of_exactChainFamilySourceGate))))

end

end RemainderDependencyFinalW31
end PachToth

namespace Verified

abbrev PachTothW31RemainderExactDependencySource : Type :=
  PachToth.RemainderDependencyFinalW31.RemainderExactDependencySource

abbrev PachTothW31RemainderExactChainSourceGate : Prop :=
  PachToth.RemainderDependencyFinalW31.ExactChainFamilySourceGate

abbrev PachTothW31RemainderExactChainDependency : Prop :=
  PachToth.RemainderDependencyFinalW31.RemainingExactChainFamilyDependency

abbrev PachTothW31RemainderExactDependencyBlocker : Prop :=
  PachToth.RemainderDependencyFinalW31.RemainingExactChainDependencyBlocker

theorem pachtoth_w31_remainderDependencySource_of_exactChainSourceGate
    (H : PachTothW31RemainderExactChainSourceGate) :
    Nonempty PachTothW31RemainderExactDependencySource :=
  PachToth.RemainderDependencyFinalW31.nonempty_source_of_exactChainFamilySourceGate
    H

theorem pachtoth_w31_remainderExactChainDependency_of_exactChainSourceGate
    (H : PachTothW31RemainderExactChainSourceGate) :
    PachTothW31RemainderExactChainDependency :=
  PachToth.RemainderDependencyFinalW31.remainingExactChainFamilyDependency_of_exactChainFamilySourceGate
    H

theorem pachtoth_w31_remainderExactSourcePackageGate_of_exactChainSourceGate
    (H : PachTothW31RemainderExactChainSourceGate) :
    PachToth.RemainderDependencyFinalW31.RemainderExactSourcePackageGate :=
  PachToth.RemainderDependencyFinalW31.remainderExactSourcePackageGate_of_exactChainFamilySourceGate
    H

theorem pachtoth_w31_remainderSplitExactSourcePackageGate_of_exactChainSourceGate
    (H : PachTothW31RemainderExactChainSourceGate) :
    PachToth.RemainderDependencyFinalW31.RemainderSplitExactSourcePackageGate :=
  PachToth.RemainderDependencyFinalW31.remainderSplitExactSourcePackageGate_of_exactChainFamilySourceGate
    H

theorem pachtoth_w31_checkedBlocker_is_exactChainSourceGate :
    PachTothW31RemainderExactDependencyBlocker <->
      PachTothW31RemainderExactChainSourceGate :=
  PachToth.RemainderDependencyFinalW31.checkedBlocker_is_exactChainFamilySourceGate

theorem pachtoth_w31_remainderDependencyClosureFinal :
    (PachTothW31RemainderExactChainSourceGate ->
      Nonempty PachTothW31RemainderExactDependencySource) /\
      (PachTothW31RemainderExactChainSourceGate ->
        PachTothW31RemainderExactChainDependency) /\
        (PachTothW31RemainderExactChainSourceGate ->
          PachToth.RemainderDependencyFinalW31.RemainderExactSourcePackageGate) /\
          (PachTothW31RemainderExactChainSourceGate ->
            PachToth.RemainderDependencyFinalW31.RemainderSplitExactSourcePackageGate) /\
            (PachTothW31RemainderExactDependencyBlocker <->
              PachTothW31RemainderExactChainSourceGate) /\
              (PachTothW31RemainderExactChainSourceGate ->
                PachToth.RemainderDependencyFinalW31.ArbitraryTarget) :=
  PachToth.RemainderDependencyFinalW31.dependencyClosureFinal

end Verified
end ErdosProblems1066
