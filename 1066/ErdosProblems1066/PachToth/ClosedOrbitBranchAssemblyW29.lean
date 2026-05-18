import ErdosProblems1066.PachToth.ExactAndArbitrarySourceAssemblyW28
import ErdosProblems1066.PachToth.LargeTailExactSourceW28
import ErdosProblems1066.PachToth.SquaredOrbitClosureSourceW28

set_option autoImplicit false

/-!
# W29 closed-orbit branch assembly

The proposed W29 helper leaves for completion rows and large-tail fields are
not present in this workspace.  This file therefore assembles the same branch
over the W28 source-facing fields:

* generated-orbit completion rows,
* squared orbit-closure source rows, and
* large-tail exact source fields together with the small exact blocks.

Each route is sent into the W28 exact/arbitrary source gate before the endpoint
projection is taken.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedOrbitBranchAssemblyW29

noncomputable section

/-! ## Endpoint and W28 gate vocabulary -/

abbrev ExactTarget : Prop :=
  ExactAndArbitrarySourceAssemblyW28.ExactTarget

abbrev ArbitraryTarget : Prop :=
  ExactAndArbitrarySourceAssemblyW28.ArbitraryTarget

abbrev ExactAndArbitraryTargets : Prop :=
  ExactAndArbitrarySourceAssemblyW28.ExactAndArbitraryTargets

abbrev ExactArbitrarySourceGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.SourceGate

abbrev ConcreteClosedOrbitFamily : Type :=
  ExactAndArbitrarySourceAssemblyW28.ConcreteClosedOrbitFamily

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.ConcreteClosedOrbitFamilyGate

abbrev RemainderExactSourceGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.RemainderExactSourceGate

abbrev PositiveExactChainPackage : Type :=
  ExactAndArbitrarySourceAssemblyW28.PositiveExactChainPackage

abbrev PositiveExactChainPackageGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.PositiveExactChainPackageGate

/-! ## W28 completion-row and closed-orbit source fields -/

abbrev GeneratedOrbitSkeleton : Type :=
  SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton

abbrev CompletionRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton.CompletionRows G

abbrev SquaredOrbitClosureSourceRows : Type :=
  SquaredOrbitClosureSourceW28.SquaredOrbitClosureSourceRows

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  SquaredOrbitClosureSourceW28.SquaredMinimalFieldsWithOrbitClosure

/-- A local W29 name for W28 generated-orbit skeletons equipped with the
completion rows needed to enter the squared closed-orbit source. -/
structure CompletionRowsSource where
  skeleton : GeneratedOrbitSkeleton
  rows : CompletionRows skeleton

namespace CompletionRowsSource

def toSquaredOrbitClosureSourceRows
    (S : CompletionRowsSource) :
    SquaredOrbitClosureSourceRows where
  skeleton := S.skeleton
  rows := S.rows

end CompletionRowsSource

abbrev CompletionRowsSourceGate : Prop :=
  Nonempty CompletionRowsSource

abbrev SquaredOrbitClosureCompletionRowsGate : Prop :=
  Nonempty SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureGate : Prop :=
  Nonempty SquaredMinimalFieldsWithOrbitClosure

def squaredOrbitClosureSourceRowsOfCompletionRows
    (G : GeneratedOrbitSkeleton) (R : CompletionRows G) :
    SquaredOrbitClosureSourceRows where
  skeleton := G
  rows := R

theorem squaredOrbitClosureCompletionRowsGate_of_completionRowsSourceGate
    (H : CompletionRowsSourceGate) :
    SquaredOrbitClosureCompletionRowsGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.toSquaredOrbitClosureSourceRows

theorem squaredOrbitClosureGate_of_squaredOrbitClosureCompletionRowsGate
    (H : SquaredOrbitClosureCompletionRowsGate) :
    SquaredOrbitClosureGate :=
  SquaredOrbitClosureSourceW28.nonempty_squaredMinimalFieldsWithOrbitClosure_of_sourceRows
    H

theorem concreteClosedOrbitFamilyGate_of_squaredOrbitClosureCompletionRowsGate
    (H : SquaredOrbitClosureCompletionRowsGate) :
    ConcreteClosedOrbitFamilyGate :=
  SquaredOrbitClosureSourceW28.nonempty_concreteClosedOrbitFamily_of_sourceRows
    H

theorem concreteClosedOrbitFamilyGate_of_completionRowsSourceGate
    (H : CompletionRowsSourceGate) :
    ConcreteClosedOrbitFamilyGate :=
  concreteClosedOrbitFamilyGate_of_squaredOrbitClosureCompletionRowsGate
    (squaredOrbitClosureCompletionRowsGate_of_completionRowsSourceGate H)

theorem exactArbitrarySourceGate_of_squaredOrbitClosureCompletionRowsGate
    (H : SquaredOrbitClosureCompletionRowsGate) :
    ExactArbitrarySourceGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (concreteClosedOrbitFamilyGate_of_squaredOrbitClosureCompletionRowsGate
          H)))

theorem exactArbitrarySourceGate_of_completionRowsSourceGate
    (H : CompletionRowsSourceGate) :
    ExactArbitrarySourceGate :=
  exactArbitrarySourceGate_of_squaredOrbitClosureCompletionRowsGate
    (squaredOrbitClosureCompletionRowsGate_of_completionRowsSourceGate H)

/-! ## W28 large-tail source fields -/

abbrev ExactBlocksOneThroughFive : Prop :=
  LargeTailExactSourceW28.ExactBlocksOneThroughFive

abbrev LargeTailExactSourcePackage : Type :=
  LargeTailExactSourceW28.LargeTailExactSourcePackage

/-- Large-tail fields become an exact-chain source only when paired with the
already checked exact blocks one through five. -/
structure LargeTailFieldsSource where
  small : ExactBlocksOneThroughFive
  tail : LargeTailExactSourcePackage

namespace LargeTailFieldsSource

def positiveExactChainPackage
    (S : LargeTailFieldsSource) :
    PositiveExactChainPackage :=
  S.tail.positiveExactChainPackage S.small

end LargeTailFieldsSource

abbrev LargeTailFieldsSourceGate : Prop :=
  Nonempty LargeTailFieldsSource

theorem positiveExactChainPackageGate_of_largeTailFieldsSourceGate
    (H : LargeTailFieldsSourceGate) :
    PositiveExactChainPackageGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.positiveExactChainPackage

theorem remainderExactSourceGate_of_largeTailFieldsSourceGate
    (H : LargeTailFieldsSourceGate) :
    RemainderExactSourceGate :=
  ExactAndArbitrarySourceAssemblyW28.remainderExactSourceGate_of_positiveExactChainPackageGate
    (positiveExactChainPackageGate_of_largeTailFieldsSourceGate H)

theorem exactArbitrarySourceGate_of_largeTailFieldsSourceGate
    (H : LargeTailFieldsSourceGate) :
    ExactArbitrarySourceGate :=
  Or.inr
    (Or.inr
      (Or.inl
        (remainderExactSourceGate_of_largeTailFieldsSourceGate H)))

/-! ## Unified branch assembly -/

abbrev ClosedOrbitBranchSourceGate : Prop :=
  CompletionRowsSourceGate \/
    SquaredOrbitClosureCompletionRowsGate \/
      LargeTailFieldsSourceGate

theorem exactArbitrarySourceGate_of_closedOrbitBranchSourceGate
    (H : ClosedOrbitBranchSourceGate) :
    ExactArbitrarySourceGate := by
  cases H with
  | inl hCompletion =>
      exact exactArbitrarySourceGate_of_completionRowsSourceGate hCompletion
  | inr hRest =>
      cases hRest with
      | inl hSquared =>
          exact exactArbitrarySourceGate_of_squaredOrbitClosureCompletionRowsGate
            hSquared
      | inr hLarge =>
          exact exactArbitrarySourceGate_of_largeTailFieldsSourceGate hLarge

theorem exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (H : ClosedOrbitBranchSourceGate) :
    ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_sourceGate
    (exactArbitrarySourceGate_of_closedOrbitBranchSourceGate H)

theorem exactAndArbitraryTargets_of_completionRowsSourceGate
    (H : CompletionRowsSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (Or.inl H)

theorem exactAndArbitraryTargets_of_squaredOrbitClosureCompletionRowsGate
    (H : SquaredOrbitClosureCompletionRowsGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (Or.inr (Or.inl H))

theorem exactAndArbitraryTargets_of_largeTailFieldsSourceGate
    (H : LargeTailFieldsSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (Or.inr (Or.inr H))

theorem conditionalAssembly :
    (ClosedOrbitBranchSourceGate -> ExactAndArbitraryTargets) /\
      (CompletionRowsSourceGate -> ExactArbitrarySourceGate) /\
        (SquaredOrbitClosureCompletionRowsGate -> ExactArbitrarySourceGate) /\
          (LargeTailFieldsSourceGate -> ExactArbitrarySourceGate) :=
  And.intro exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (And.intro exactArbitrarySourceGate_of_completionRowsSourceGate
      (And.intro exactArbitrarySourceGate_of_squaredOrbitClosureCompletionRowsGate
        exactArbitrarySourceGate_of_largeTailFieldsSourceGate))

end

end ClosedOrbitBranchAssemblyW29
end PachToth

namespace Verified

abbrev PachTothW29CompletionRowsSource : Type :=
  PachToth.ClosedOrbitBranchAssemblyW29.CompletionRowsSource

abbrev PachTothW29SquaredOrbitClosureCompletionRowsGate : Prop :=
  PachToth.ClosedOrbitBranchAssemblyW29.SquaredOrbitClosureCompletionRowsGate

abbrev PachTothW29LargeTailFieldsSource : Type :=
  PachToth.ClosedOrbitBranchAssemblyW29.LargeTailFieldsSource

abbrev PachTothW29ClosedOrbitBranchSourceGate : Prop :=
  PachToth.ClosedOrbitBranchAssemblyW29.ClosedOrbitBranchSourceGate

theorem pachtoth_w29_exactArbitrarySourceGate_of_closedOrbitBranchSourceGate
    (H : PachTothW29ClosedOrbitBranchSourceGate) :
    PachToth.ClosedOrbitBranchAssemblyW29.ExactArbitrarySourceGate :=
  PachToth.ClosedOrbitBranchAssemblyW29.exactArbitrarySourceGate_of_closedOrbitBranchSourceGate
    H

theorem pachtoth_w29_exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (H : PachTothW29ClosedOrbitBranchSourceGate) :
    PachToth.ClosedOrbitBranchAssemblyW29.ExactAndArbitraryTargets :=
  PachToth.ClosedOrbitBranchAssemblyW29.exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    H

theorem pachtoth_w29_conditionalAssembly :
    (PachTothW29ClosedOrbitBranchSourceGate ->
      PachToth.ClosedOrbitBranchAssemblyW29.ExactAndArbitraryTargets) /\
      (Nonempty PachTothW29CompletionRowsSource ->
        PachToth.ClosedOrbitBranchAssemblyW29.ExactArbitrarySourceGate) /\
        (PachTothW29SquaredOrbitClosureCompletionRowsGate ->
          PachToth.ClosedOrbitBranchAssemblyW29.ExactArbitrarySourceGate) /\
          (Nonempty PachTothW29LargeTailFieldsSource ->
            PachToth.ClosedOrbitBranchAssemblyW29.ExactArbitrarySourceGate) :=
  PachToth.ClosedOrbitBranchAssemblyW29.conditionalAssembly

end Verified
end ErdosProblems1066
