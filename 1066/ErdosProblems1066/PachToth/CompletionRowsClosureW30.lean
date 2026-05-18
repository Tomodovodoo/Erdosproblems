import ErdosProblems1066.PachToth.PachTothW29RouteAudit

set_option autoImplicit false

/-!
# W30 completion-row closure

This file packages the W29 completion-row handoff from generated-closure metric
rows through the squared closed-orbit source, then exposes the downstream
concrete closed-orbit and exact/arbitrary gates.  All constructors below move
from named source data toward the target gates; none recover source rows from a
target statement.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CompletionRowsClosureW30

noncomputable section

/-! ## Source and endpoint vocabulary -/

abbrev GeneratedOrbitSkeleton : Type :=
  SquaredOrbitClosureCompletionRowsW29.GeneratedOrbitSkeleton

abbrev GeneratedClosureMetricRowPackage : Type :=
  CompletionRowsSourceW29.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  Nonempty GeneratedClosureMetricRowPackage

abbrev DisplacementClosureRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.DisplacementClosureRows G

abbrev SeparationRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.SeparationRows G

abbrev SameBlockUnitRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.SameBlockUnitRows G

abbrev CompletionRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.CompletionRows G

abbrev GeneratedCompletionRowsGate (G : GeneratedOrbitSkeleton) : Prop :=
  Nonempty (CompletionRows G)

abbrev AnyGeneratedCompletionRowsGate : Prop :=
  Exists fun G : GeneratedOrbitSkeleton => GeneratedCompletionRowsGate G

abbrev SquaredOrbitClosureSourceRows : Type :=
  SquaredOrbitClosureCompletionRowsW29.SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  Nonempty SquaredOrbitClosureSourceRows

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  SquaredOrbitClosureCompletionRowsW29.SquaredMinimalFieldsWithOrbitClosure

abbrev SquaredOrbitClosureGate : Prop :=
  Nonempty SquaredMinimalFieldsWithOrbitClosure

abbrev ConcreteClosedOrbitFamily : Type :=
  SquaredOrbitClosureCompletionRowsW29.ConcreteClosedOrbitFamily

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  Nonempty ConcreteClosedOrbitFamily

abbrev MinimalFreePlacementFields : Type :=
  SquaredOrbitClosureCompletionRowsW29.MinimalFreePlacementFields

abbrev MinimalFreePlacementFieldsGate : Prop :=
  Nonempty MinimalFreePlacementFields

abbrev ClosedOrbitBranchGate : Prop :=
  PachTothW29RouteAudit.ClosedOrbitBranchGate

abbrev ExactArbitrarySourceGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.SourceGate

abbrev ExactTarget : Prop :=
  PachTothW29RouteAudit.ExactTarget

abbrev ArbitraryTarget : Prop :=
  PachTothW29RouteAudit.ArbitraryTarget

abbrev ExactAndArbitraryTargets : Prop :=
  PachTothW29RouteAudit.ExactAndArbitraryTargets

/-! ## Generated metric rows as completion-row sources -/

def skeletonOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    GeneratedOrbitSkeleton :=
  CompletionRowsSourceW29.skeletonOfGeneratedClosureMetricRowPackage P

def completionRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    CompletionRows (skeletonOfGeneratedClosureMetricRowPackage P) :=
  CompletionRowsSourceW29.completionRowsOfGeneratedClosureMetricRowPackage P

def sourceRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    SquaredOrbitClosureSourceRows :=
  SquaredOrbitClosureCompletionRowsW29.sourceRowsOfGeneratedClosureMetricRowPackage
    P

/-- A source-side W30 package: generated metric rows together with the
completion rows they induce for the same skeleton. -/
structure GeneratedClosureCompletionRowsSource where
  package : GeneratedClosureMetricRowPackage
  rows : CompletionRows (skeletonOfGeneratedClosureMetricRowPackage package)

namespace GeneratedClosureCompletionRowsSource

def ofPackage
    (P : GeneratedClosureMetricRowPackage) :
    GeneratedClosureCompletionRowsSource where
  package := P
  rows := completionRowsOfGeneratedClosureMetricRowPackage P

def toSourceRows
    (S : GeneratedClosureCompletionRowsSource) :
    SquaredOrbitClosureSourceRows :=
  SquaredOrbitClosureCompletionRowsW29.sourceRowsOfCompletionRows
    (skeletonOfGeneratedClosureMetricRowPackage S.package) S.rows

def toSquaredMinimalFieldsWithOrbitClosure
    (S : GeneratedClosureCompletionRowsSource) :
    SquaredMinimalFieldsWithOrbitClosure :=
  S.toSourceRows.toSquaredMinimalFieldsWithOrbitClosure

def toConcreteClosedOrbitFamily
    (S : GeneratedClosureCompletionRowsSource) :
    ConcreteClosedOrbitFamily :=
  S.toSourceRows.toConcreteClosedOrbitFamily

def toMinimalFreePlacementFields
    (S : GeneratedClosureCompletionRowsSource) :
    MinimalFreePlacementFields :=
  S.toConcreteClosedOrbitFamily.toMinimalFreePlacementFields

@[simp]
theorem toSourceRows_skeleton
    (S : GeneratedClosureCompletionRowsSource) :
    S.toSourceRows.skeleton =
      skeletonOfGeneratedClosureMetricRowPackage S.package :=
  rfl

@[simp]
theorem ofPackage_package
    (P : GeneratedClosureMetricRowPackage) :
    (ofPackage P).package = P :=
  rfl

@[simp]
theorem ofPackage_rows
    (P : GeneratedClosureMetricRowPackage) :
    (ofPackage P).rows =
      completionRowsOfGeneratedClosureMetricRowPackage P :=
  rfl

end GeneratedClosureCompletionRowsSource

theorem generatedClosureCompletionRowsSourceGate_iff_generatedClosureMetricGate :
    Nonempty GeneratedClosureCompletionRowsSource <->
      GeneratedClosureMetricGate := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.package
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (GeneratedClosureCompletionRowsSource.ofPackage P)

theorem generatedClosureMetricGate_iff_generatedClosureCompletionRowsSourceGate :
    GeneratedClosureMetricGate <->
      Nonempty GeneratedClosureCompletionRowsSource :=
  generatedClosureCompletionRowsSourceGate_iff_generatedClosureMetricGate.symm

theorem anyGeneratedCompletionRowsGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    AnyGeneratedCompletionRowsGate := by
  cases H with
  | intro P =>
      exact
        Exists.intro (skeletonOfGeneratedClosureMetricRowPackage P)
          (Nonempty.intro
            (completionRowsOfGeneratedClosureMetricRowPackage P))

theorem generatedClosureMetricGate_iff_source_completionRowsSource :
    GeneratedClosureMetricGate <->
      Exists fun S : GeneratedClosureCompletionRowsSource =>
        S.rows =
          completionRowsOfGeneratedClosureMetricRowPackage S.package := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro (GeneratedClosureCompletionRowsSource.ofPackage P) rfl
  case mpr =>
    intro h
    cases h with
    | intro S _ =>
        exact Nonempty.intro S.package

/-! ## Completion-row source gates -/

theorem completionRowsGate_iff_source_rows
    (G : GeneratedOrbitSkeleton) :
    GeneratedCompletionRowsGate G <->
      DisplacementClosureRows G /\
        SeparationRows G /\
          SameBlockUnitRows G :=
  CompletionRowsSourceW29.completionRows_nonempty_iff_source_rows G

def completionRowsOfSourceRows
    {G : GeneratedOrbitSkeleton}
    (closure : DisplacementClosureRows G)
    (separated_sq : SeparationRows G)
    (same_block_edges_sq_unit : SameBlockUnitRows G) :
    CompletionRows G :=
  SquaredOrbitClosureCompletionRowsW29.completionRowsOfDisplacementClosureSeparation
    closure separated_sq same_block_edges_sq_unit

def sourceRowsOfCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : CompletionRows G) :
    SquaredOrbitClosureSourceRows :=
  SquaredOrbitClosureCompletionRowsW29.sourceRowsOfCompletionRows G R

theorem sourceRowsGate_of_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionRowsGate G) :
    SquaredOrbitClosureSourceRowsGate :=
  SquaredOrbitClosureCompletionRowsW29.nonempty_sourceRows_of_completionRows H

theorem sourceRowsGate_of_anyCompletionRowsGate
    (H : AnyGeneratedCompletionRowsGate) :
    SquaredOrbitClosureSourceRowsGate := by
  cases H with
  | intro G hG =>
      exact sourceRowsGate_of_completionRowsGate hG

theorem sourceRowsGate_of_generatedClosureCompletionRowsSourceGate
    (H : Nonempty GeneratedClosureCompletionRowsSource) :
    SquaredOrbitClosureSourceRowsGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.toSourceRows

theorem sourceRowsGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    SquaredOrbitClosureSourceRowsGate :=
  sourceRowsGate_of_generatedClosureCompletionRowsSourceGate
    (generatedClosureMetricGate_iff_generatedClosureCompletionRowsSourceGate.mp
      H)

theorem sourceRowsGate_of_generatedClosureMetricGate_eq_w29
    (H : GeneratedClosureMetricGate) :
    sourceRowsGate_of_generatedClosureMetricGate H =
      PachTothW29RouteAudit.squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate
        H :=
  rfl

/-! ## Concrete closed-orbit gates -/

theorem squaredOrbitClosureGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    SquaredOrbitClosureGate :=
  SquaredOrbitClosureSourceW28.nonempty_squaredMinimalFieldsWithOrbitClosure_of_sourceRows
    H

theorem concreteClosedOrbitFamilyGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    ConcreteClosedOrbitFamilyGate :=
  SquaredOrbitClosureSourceW28.nonempty_concreteClosedOrbitFamily_of_sourceRows
    H

theorem minimalFreePlacementFieldsGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    MinimalFreePlacementFieldsGate :=
  SquaredOrbitClosureSourceW28.nonempty_minimalFreePlacementFields_of_sourceRows
    H

theorem concreteClosedOrbitFamilyGate_of_generatedClosureCompletionRowsSourceGate
    (H : Nonempty GeneratedClosureCompletionRowsSource) :
    ConcreteClosedOrbitFamilyGate :=
  concreteClosedOrbitFamilyGate_of_sourceRowsGate
    (sourceRowsGate_of_generatedClosureCompletionRowsSourceGate H)

theorem concreteClosedOrbitFamilyGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ConcreteClosedOrbitFamilyGate :=
  concreteClosedOrbitFamilyGate_of_sourceRowsGate
    (sourceRowsGate_of_generatedClosureMetricGate H)

theorem concreteClosedOrbitFamilyGate_of_anyCompletionRowsGate
    (H : AnyGeneratedCompletionRowsGate) :
    ConcreteClosedOrbitFamilyGate :=
  concreteClosedOrbitFamilyGate_of_sourceRowsGate
    (sourceRowsGate_of_anyCompletionRowsGate H)

theorem closedOrbitBranchGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    ClosedOrbitBranchGate :=
  PachTothW29RouteAudit.closedOrbitBranchGate_of_sourceRowsGate H

theorem closedOrbitBranchGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_sourceRowsGate
    (sourceRowsGate_of_generatedClosureMetricGate H)

/-! ## Exact/arbitrary gates and endpoints -/

theorem exactArbitrarySourceGate_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    ExactArbitrarySourceGate :=
  Or.inr (Or.inr (Or.inr H))

theorem exactArbitrarySourceGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    ExactArbitrarySourceGate :=
  exactArbitrarySourceGate_of_concreteClosedOrbitFamilyGate
    (concreteClosedOrbitFamilyGate_of_sourceRowsGate H)

theorem exactArbitrarySourceGate_of_generatedClosureCompletionRowsSourceGate
    (H : Nonempty GeneratedClosureCompletionRowsSource) :
    ExactArbitrarySourceGate :=
  exactArbitrarySourceGate_of_sourceRowsGate
    (sourceRowsGate_of_generatedClosureCompletionRowsSourceGate H)

theorem exactArbitrarySourceGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ExactArbitrarySourceGate :=
  exactArbitrarySourceGate_of_sourceRowsGate
    (sourceRowsGate_of_generatedClosureMetricGate H)

theorem exactAndArbitraryTargets_of_exactArbitrarySourceGate
    (H : ExactArbitrarySourceGate) :
    ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_sourceGate H

theorem exactAndArbitraryTargets_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_exactArbitrarySourceGate
    (exactArbitrarySourceGate_of_sourceRowsGate H)

theorem exactAndArbitraryTargets_of_generatedClosureCompletionRowsSourceGate
    (H : Nonempty GeneratedClosureCompletionRowsSource) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_sourceRowsGate
    (sourceRowsGate_of_generatedClosureCompletionRowsSourceGate H)

theorem exactAndArbitraryTargets_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_sourceRowsGate
    (sourceRowsGate_of_generatedClosureMetricGate H)

theorem exactTarget_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ExactTarget :=
  (exactAndArbitraryTargets_of_generatedClosureMetricGate H).1

theorem arbitraryTarget_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ArbitraryTarget :=
  (exactAndArbitraryTargets_of_generatedClosureMetricGate H).2

theorem closureSummary :
    (GeneratedClosureMetricGate <->
      Nonempty GeneratedClosureCompletionRowsSource) /\
      (GeneratedClosureMetricGate -> SquaredOrbitClosureSourceRowsGate) /\
        (GeneratedClosureMetricGate -> ConcreteClosedOrbitFamilyGate) /\
          (GeneratedClosureMetricGate -> ExactArbitrarySourceGate) /\
            (GeneratedClosureMetricGate -> ExactAndArbitraryTargets) :=
  And.intro generatedClosureMetricGate_iff_generatedClosureCompletionRowsSourceGate
    (And.intro sourceRowsGate_of_generatedClosureMetricGate
      (And.intro concreteClosedOrbitFamilyGate_of_generatedClosureMetricGate
        (And.intro exactArbitrarySourceGate_of_generatedClosureMetricGate
          exactAndArbitraryTargets_of_generatedClosureMetricGate)))

end

end CompletionRowsClosureW30
end PachToth

namespace Verified

abbrev PachTothW30GeneratedClosureCompletionRowsSource : Type :=
  PachToth.CompletionRowsClosureW30.GeneratedClosureCompletionRowsSource

abbrev PachTothW30GeneratedClosureMetricGate : Prop :=
  PachToth.CompletionRowsClosureW30.GeneratedClosureMetricGate

abbrev PachTothW30SquaredOrbitClosureSourceRowsGate : Prop :=
  PachToth.CompletionRowsClosureW30.SquaredOrbitClosureSourceRowsGate

abbrev PachTothW30ConcreteClosedOrbitFamilyGate : Prop :=
  PachToth.CompletionRowsClosureW30.ConcreteClosedOrbitFamilyGate

abbrev PachTothW30ExactArbitrarySourceGate : Prop :=
  PachToth.CompletionRowsClosureW30.ExactArbitrarySourceGate

theorem pachtoth_w30_generatedClosureMetricGate_iff_completionRowsSource :
    PachTothW30GeneratedClosureMetricGate <->
      Nonempty PachTothW30GeneratedClosureCompletionRowsSource :=
  PachToth.CompletionRowsClosureW30.generatedClosureMetricGate_iff_generatedClosureCompletionRowsSourceGate

theorem pachtoth_w30_sourceRowsGate_of_generatedClosureMetricGate
    (H : PachTothW30GeneratedClosureMetricGate) :
    PachTothW30SquaredOrbitClosureSourceRowsGate :=
  PachToth.CompletionRowsClosureW30.sourceRowsGate_of_generatedClosureMetricGate H

theorem pachtoth_w30_concreteClosedOrbitFamilyGate_of_generatedClosureMetricGate
    (H : PachTothW30GeneratedClosureMetricGate) :
    PachTothW30ConcreteClosedOrbitFamilyGate :=
  PachToth.CompletionRowsClosureW30.concreteClosedOrbitFamilyGate_of_generatedClosureMetricGate
    H

theorem pachtoth_w30_exactArbitrarySourceGate_of_generatedClosureMetricGate
    (H : PachTothW30GeneratedClosureMetricGate) :
    PachTothW30ExactArbitrarySourceGate :=
  PachToth.CompletionRowsClosureW30.exactArbitrarySourceGate_of_generatedClosureMetricGate
    H

theorem pachtoth_w30_exactAndArbitraryTargets_of_generatedClosureMetricGate
    (H : PachTothW30GeneratedClosureMetricGate) :
    PachToth.CompletionRowsClosureW30.ExactAndArbitraryTargets :=
  PachToth.CompletionRowsClosureW30.exactAndArbitraryTargets_of_generatedClosureMetricGate
    H

theorem pachtoth_w30_completionRowsClosureSummary :
    (PachTothW30GeneratedClosureMetricGate <->
      Nonempty PachTothW30GeneratedClosureCompletionRowsSource) /\
      (PachTothW30GeneratedClosureMetricGate ->
        PachTothW30SquaredOrbitClosureSourceRowsGate) /\
        (PachTothW30GeneratedClosureMetricGate ->
          PachTothW30ConcreteClosedOrbitFamilyGate) /\
          (PachTothW30GeneratedClosureMetricGate ->
            PachTothW30ExactArbitrarySourceGate) /\
            (PachTothW30GeneratedClosureMetricGate ->
              PachToth.CompletionRowsClosureW30.ExactAndArbitraryTargets) :=
  PachToth.CompletionRowsClosureW30.closureSummary

end Verified
end ErdosProblems1066
