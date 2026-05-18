import ErdosProblems1066.PachToth.CompletionRowsClosureW30
import ErdosProblems1066.PachToth.GeneratedClosureMetricRowsW30

set_option autoImplicit false

/-!
# W31 completion-row inhabitation source layer

This file keeps the W30 completion-row gates tied to the actual row data they
need.  The central package is just the three source rows required by generated
completion rows: cyclic displacement closure, square-distance separation, and
same-block unit square-distance rows.

All equivalences below are record-unpacking equivalences between source-side
packages.  Generated metric rows are used only in the forward direction to
construct row data for their generated skeleton.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CompletionRowsInhabitationW31

noncomputable section

/-! ## Source vocabulary -/

abbrev GeneratedOrbitSkeleton : Type :=
  CompletionRowsClosureW30.GeneratedOrbitSkeleton

abbrev GeneratedClosureMetricRowPackage : Type :=
  CompletionRowsClosureW30.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  CompletionRowsClosureW30.GeneratedClosureMetricGate

abbrev DisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsClosureW30.DisplacementClosureRows G

abbrev SeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsClosureW30.SeparationRows G

abbrev SameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsClosureW30.SameBlockUnitRows G

abbrev CompletionRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsClosureW30.CompletionRows G

abbrev GeneratedCompletionRowsGate
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsClosureW30.GeneratedCompletionRowsGate G

abbrev AnyGeneratedCompletionRowsGate : Prop :=
  CompletionRowsClosureW30.AnyGeneratedCompletionRowsGate

abbrev SquaredOrbitClosureSourceRows : Type :=
  CompletionRowsClosureW30.SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  CompletionRowsClosureW30.SquaredOrbitClosureSourceRowsGate

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  CompletionRowsClosureW30.SquaredMinimalFieldsWithOrbitClosure

abbrev ConcreteClosedOrbitFamily : Type :=
  CompletionRowsClosureW30.ConcreteClosedOrbitFamily

abbrev MinimalFreePlacementFields : Type :=
  CompletionRowsClosureW30.MinimalFreePlacementFields

abbrev GeneratedClosureCompletionRowsSource : Type :=
  CompletionRowsClosureW30.GeneratedClosureCompletionRowsSource

/-! ## Exact completion-row data -/

/-- The exact row data needed to inhabit generated completion rows for a
fixed generated skeleton. -/
structure GeneratedCompletionRowData
    (G : GeneratedOrbitSkeleton) where
  closure : DisplacementClosureRows G
  separated_sq : SeparationRows G
  same_block_edges_sq_unit : SameBlockUnitRows G

namespace GeneratedCompletionRowData

def toCompletionRows
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    CompletionRows G where
  closure := D.closure
  separated_sq := D.separated_sq
  same_block_edges_sq_unit := D.same_block_edges_sq_unit

def ofCompletionRows
    {G : GeneratedOrbitSkeleton}
    (R : CompletionRows G) :
    GeneratedCompletionRowData G where
  closure := R.closure
  separated_sq := R.separated_sq
  same_block_edges_sq_unit := R.same_block_edges_sq_unit

def toSourceRows
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    SquaredOrbitClosureSourceRows :=
  CompletionRowsClosureW30.sourceRowsOfCompletionRows G
    D.toCompletionRows

def toSquaredMinimalFieldsWithOrbitClosure
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    SquaredMinimalFieldsWithOrbitClosure :=
  D.toSourceRows.toSquaredMinimalFieldsWithOrbitClosure

def toConcreteClosedOrbitFamily
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    ConcreteClosedOrbitFamily :=
  D.toSourceRows.toConcreteClosedOrbitFamily

def toMinimalFreePlacementFields
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    MinimalFreePlacementFields :=
  D.toConcreteClosedOrbitFamily.toMinimalFreePlacementFields

@[simp]
theorem toCompletionRows_closure
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    D.toCompletionRows.closure = D.closure :=
  rfl

@[simp]
theorem toCompletionRows_separated_sq
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    D.toCompletionRows.separated_sq = D.separated_sq :=
  rfl

@[simp]
theorem toCompletionRows_same_block_edges_sq_unit
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    D.toCompletionRows.same_block_edges_sq_unit =
      D.same_block_edges_sq_unit :=
  rfl

@[simp]
theorem ofCompletionRows_closure
    {G : GeneratedOrbitSkeleton}
    (R : CompletionRows G) :
    (ofCompletionRows R).closure = R.closure :=
  rfl

@[simp]
theorem ofCompletionRows_separated_sq
    {G : GeneratedOrbitSkeleton}
    (R : CompletionRows G) :
    (ofCompletionRows R).separated_sq = R.separated_sq :=
  rfl

@[simp]
theorem ofCompletionRows_same_block_edges_sq_unit
    {G : GeneratedOrbitSkeleton}
    (R : CompletionRows G) :
    (ofCompletionRows R).same_block_edges_sq_unit =
      R.same_block_edges_sq_unit :=
  rfl

@[simp]
theorem toSourceRows_skeleton
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    D.toSourceRows.skeleton = G :=
  rfl

end GeneratedCompletionRowData

theorem nonempty_generatedCompletionRowData_iff_completionRowsGate
    (G : GeneratedOrbitSkeleton) :
    Nonempty (GeneratedCompletionRowData G) <->
      GeneratedCompletionRowsGate G := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro D.toCompletionRows
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact
          Nonempty.intro
            (GeneratedCompletionRowData.ofCompletionRows R)

theorem completionRowsGate_iff_generatedCompletionRowData
    (G : GeneratedOrbitSkeleton) :
    GeneratedCompletionRowsGate G <->
      Nonempty (GeneratedCompletionRowData G) :=
  (nonempty_generatedCompletionRowData_iff_completionRowsGate G).symm

theorem nonempty_generatedCompletionRowData_iff_source_rows
    (G : GeneratedOrbitSkeleton) :
    Nonempty (GeneratedCompletionRowData G) <->
      DisplacementClosureRows G /\
        SeparationRows G /\
          SameBlockUnitRows G := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact
          And.intro D.closure
            (And.intro D.separated_sq D.same_block_edges_sq_unit)
  case mpr =>
    intro h
    exact
      Nonempty.intro
        { closure := h.1
          separated_sq := h.2.1
          same_block_edges_sq_unit := h.2.2 }

/-! ## Source rows as completion-row inhabitants -/

/-- A skeleton paired with its exact completion-row data. -/
structure GeneratedCompletionRowSource where
  skeleton : GeneratedOrbitSkeleton
  data : GeneratedCompletionRowData skeleton

namespace GeneratedCompletionRowSource

def toCompletionRows
    (S : GeneratedCompletionRowSource) :
    CompletionRows S.skeleton :=
  S.data.toCompletionRows

def toSourceRows
    (S : GeneratedCompletionRowSource) :
    SquaredOrbitClosureSourceRows :=
  S.data.toSourceRows

def ofCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : CompletionRows G) :
    GeneratedCompletionRowSource where
  skeleton := G
  data := GeneratedCompletionRowData.ofCompletionRows R

def ofSourceRows
    (S : SquaredOrbitClosureSourceRows) :
    GeneratedCompletionRowSource where
  skeleton := S.skeleton
  data := GeneratedCompletionRowData.ofCompletionRows S.rows

def toSquaredMinimalFieldsWithOrbitClosure
    (S : GeneratedCompletionRowSource) :
    SquaredMinimalFieldsWithOrbitClosure :=
  S.data.toSquaredMinimalFieldsWithOrbitClosure

def toConcreteClosedOrbitFamily
    (S : GeneratedCompletionRowSource) :
    ConcreteClosedOrbitFamily :=
  S.data.toConcreteClosedOrbitFamily

def toMinimalFreePlacementFields
    (S : GeneratedCompletionRowSource) :
    MinimalFreePlacementFields :=
  S.data.toMinimalFreePlacementFields

@[simp]
theorem toSourceRows_skeleton
    (S : GeneratedCompletionRowSource) :
    S.toSourceRows.skeleton = S.skeleton :=
  rfl

@[simp]
theorem ofSourceRows_skeleton
    (S : SquaredOrbitClosureSourceRows) :
    (ofSourceRows S).skeleton = S.skeleton :=
  rfl

end GeneratedCompletionRowSource

theorem nonempty_generatedCompletionRowSource_iff_anyCompletionRowsGate :
    Nonempty GeneratedCompletionRowSource <->
      AnyGeneratedCompletionRowsGate := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.skeleton
            (Nonempty.intro S.toCompletionRows)
  case mpr =>
    intro h
    cases h with
    | intro G hG =>
        cases hG with
        | intro R =>
            exact
              Nonempty.intro
                (GeneratedCompletionRowSource.ofCompletionRows G R)

theorem nonempty_generatedCompletionRowSource_iff_sourceRowsGate :
    Nonempty GeneratedCompletionRowSource <->
      SquaredOrbitClosureSourceRowsGate := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toSourceRows
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact
          Nonempty.intro
            (GeneratedCompletionRowSource.ofSourceRows S)

/-! ## Constructors from generated metric and squared-orbit rows -/

def generatedCompletionRowDataOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    GeneratedCompletionRowData
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        P) :=
  GeneratedCompletionRowData.ofCompletionRows
    (CompletionRowsClosureW30.completionRowsOfGeneratedClosureMetricRowPackage
      P)

def generatedCompletionRowSourceOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    GeneratedCompletionRowSource where
  skeleton :=
    CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage P
  data := generatedCompletionRowDataOfGeneratedClosureMetricRowPackage P

def generatedCompletionRowSourceOfGeneratedClosureCompletionRowsSource
    (S : GeneratedClosureCompletionRowsSource) :
    GeneratedCompletionRowSource where
  skeleton :=
    CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
      S.package
  data := GeneratedCompletionRowData.ofCompletionRows S.rows

def generatedCompletionRowSourceOfSquaredOrbitClosureSourceRows
    (S : SquaredOrbitClosureSourceRows) :
    GeneratedCompletionRowSource :=
  GeneratedCompletionRowSource.ofSourceRows S

theorem generatedCompletionRowSourceGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    Nonempty GeneratedCompletionRowSource := by
  cases H with
  | intro P =>
      exact
        Nonempty.intro
          (generatedCompletionRowSourceOfGeneratedClosureMetricRowPackage P)

theorem generatedCompletionRowSourceGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    Nonempty GeneratedCompletionRowSource :=
  (nonempty_generatedCompletionRowSource_iff_sourceRowsGate).mpr H

theorem sourceRowsGate_of_generatedCompletionRowSourceGate
    (H : Nonempty GeneratedCompletionRowSource) :
    SquaredOrbitClosureSourceRowsGate :=
  (nonempty_generatedCompletionRowSource_iff_sourceRowsGate).mp H

theorem anyCompletionRowsGate_of_generatedCompletionRowSourceGate
    (H : Nonempty GeneratedCompletionRowSource) :
    AnyGeneratedCompletionRowsGate :=
  (nonempty_generatedCompletionRowSource_iff_anyCompletionRowsGate).mp H

theorem generatedCompletionRowSourceGate_of_anyCompletionRowsGate
    (H : AnyGeneratedCompletionRowsGate) :
    Nonempty GeneratedCompletionRowSource :=
  (nonempty_generatedCompletionRowSource_iff_anyCompletionRowsGate).mpr H

theorem sourceRowsGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    SquaredOrbitClosureSourceRowsGate :=
  sourceRowsGate_of_generatedCompletionRowSourceGate
    (generatedCompletionRowSourceGate_of_generatedClosureMetricGate H)

/-! ## Existing W30 generated metric row constructors -/

abbrev GeneratedChainFamily : Type :=
  GeneratedClosureMetricRowsW30.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedClosureMetricRowsW30.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedClosureMetricRowsW30.ReducedMetricHypotheses F

abbrev W20SourceFields : Type :=
  GeneratedClosureMetricRowsW30.W20SourceFields

abbrev AlternativeValueMatrixFamily : Type :=
  GeneratedClosureMetricRowsW30.AlternativeValueMatrixFamily

abbrev NonRoleDirectSourceMissingPackage : Type :=
  GeneratedClosureMetricRowsW30.NonRoleDirectSourceMissingPackage

def generatedCompletionRowSourceOfClosureReducedMetric
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (metric : ReducedMetricHypotheses F) :
    GeneratedCompletionRowSource :=
  generatedCompletionRowSourceOfGeneratedClosureMetricRowPackage
    (GeneratedClosureMetricRowsW30.generatedClosureMetricRowPackageOfClosureReducedMetric
      F closure metric)

def generatedCompletionRowSourceOfW20SourceFields
    (S : W20SourceFields) :
    GeneratedCompletionRowSource :=
  generatedCompletionRowSourceOfGeneratedClosureMetricRowPackage
    (GeneratedClosureMetricRowsW30.generatedClosureMetricRowPackageOfW20SourceFields
      S)

def generatedCompletionRowSourceOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    GeneratedCompletionRowSource :=
  generatedCompletionRowSourceOfGeneratedClosureMetricRowPackage
    (GeneratedClosureMetricRowsW30.generatedClosureMetricRowPackageOfAlternativeValueMatrixFamily
      A)

def generatedCompletionRowSourceOfNonRoleDirectSourceMissingPackage
    (P : NonRoleDirectSourceMissingPackage) :
    GeneratedCompletionRowSource :=
  generatedCompletionRowSourceOfGeneratedClosureMetricRowPackage
    (GeneratedClosureMetricRowsW30.generatedClosureMetricRowPackageOfNonRoleDirectSourceMissingPackage
      P)

/-! ## Record-unpacking bridge to the W30 completion-row source package -/

structure GeneratedMetricCompletionRowData where
  package : GeneratedClosureMetricRowPackage
  data :
    GeneratedCompletionRowData
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        package)

namespace GeneratedMetricCompletionRowData

def ofPackage
    (P : GeneratedClosureMetricRowPackage) :
    GeneratedMetricCompletionRowData where
  package := P
  data := generatedCompletionRowDataOfGeneratedClosureMetricRowPackage P

def toW30Source
    (S : GeneratedMetricCompletionRowData) :
    GeneratedClosureCompletionRowsSource where
  package := S.package
  rows := S.data.toCompletionRows

def ofW30Source
    (S : GeneratedClosureCompletionRowsSource) :
    GeneratedMetricCompletionRowData where
  package := S.package
  data := GeneratedCompletionRowData.ofCompletionRows S.rows

@[simp]
theorem ofPackage_package
    (P : GeneratedClosureMetricRowPackage) :
    (ofPackage P).package = P :=
  rfl

@[simp]
theorem toW30Source_package
    (S : GeneratedMetricCompletionRowData) :
    S.toW30Source.package = S.package :=
  rfl

@[simp]
theorem ofW30Source_package
    (S : GeneratedClosureCompletionRowsSource) :
    (ofW30Source S).package = S.package :=
  rfl

end GeneratedMetricCompletionRowData

theorem nonempty_generatedMetricCompletionRowData_iff_w30Source :
    Nonempty GeneratedMetricCompletionRowData <->
      Nonempty GeneratedClosureCompletionRowsSource := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toW30Source
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact
          Nonempty.intro
            (GeneratedMetricCompletionRowData.ofW30Source S)

theorem generatedMetricCompletionRowData_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    Nonempty GeneratedMetricCompletionRowData := by
  cases H with
  | intro P =>
      exact
        Nonempty.intro
          (GeneratedMetricCompletionRowData.ofPackage P)

/-! ## Compact W31 source-only certificate -/

abbrev CompletionRowsInhabitationCertificate : Prop :=
  (forall G : GeneratedOrbitSkeleton,
    Nonempty (GeneratedCompletionRowData G) <->
      GeneratedCompletionRowsGate G) /\
    (Nonempty GeneratedCompletionRowSource <->
      SquaredOrbitClosureSourceRowsGate) /\
      (GeneratedClosureMetricGate ->
        Nonempty GeneratedCompletionRowSource) /\
        (Nonempty GeneratedMetricCompletionRowData <->
          Nonempty GeneratedClosureCompletionRowsSource)

theorem completionRowsInhabitationCertificate :
    CompletionRowsInhabitationCertificate := by
  exact
    And.intro nonempty_generatedCompletionRowData_iff_completionRowsGate
      (And.intro nonempty_generatedCompletionRowSource_iff_sourceRowsGate
        (And.intro
          generatedCompletionRowSourceGate_of_generatedClosureMetricGate
          nonempty_generatedMetricCompletionRowData_iff_w30Source))

end

end CompletionRowsInhabitationW31
end PachToth

namespace Verified

abbrev PachTothW31GeneratedCompletionRowSource : Type :=
  PachToth.CompletionRowsInhabitationW31.GeneratedCompletionRowSource

abbrev PachTothW31GeneratedMetricCompletionRowData : Type :=
  PachToth.CompletionRowsInhabitationW31.GeneratedMetricCompletionRowData

abbrev PachTothW31SquaredOrbitClosureSourceRowsGate : Prop :=
  PachToth.CompletionRowsInhabitationW31.SquaredOrbitClosureSourceRowsGate

theorem pachtoth_w31_completionRowSource_iff_sourceRowsGate :
    Nonempty PachTothW31GeneratedCompletionRowSource <->
      PachTothW31SquaredOrbitClosureSourceRowsGate :=
  PachToth.CompletionRowsInhabitationW31.nonempty_generatedCompletionRowSource_iff_sourceRowsGate

theorem pachtoth_w31_completionRowSource_of_generatedClosureMetricGate
    (H : PachToth.CompletionRowsInhabitationW31.GeneratedClosureMetricGate) :
    Nonempty PachTothW31GeneratedCompletionRowSource :=
  PachToth.CompletionRowsInhabitationW31.generatedCompletionRowSourceGate_of_generatedClosureMetricGate
    H

theorem pachtoth_w31_generatedMetricCompletionRowData_iff_w30Source :
    Nonempty PachTothW31GeneratedMetricCompletionRowData <->
      Nonempty
        PachToth.CompletionRowsInhabitationW31.GeneratedClosureCompletionRowsSource :=
  PachToth.CompletionRowsInhabitationW31.nonempty_generatedMetricCompletionRowData_iff_w30Source

theorem pachtoth_w31_completionRowsInhabitationCertificate :
    PachToth.CompletionRowsInhabitationW31.CompletionRowsInhabitationCertificate :=
  PachToth.CompletionRowsInhabitationW31.completionRowsInhabitationCertificate

end Verified
end ErdosProblems1066
