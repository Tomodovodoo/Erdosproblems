import ErdosProblems1066.PachToth.CompletionRowsInhabitationW31
import ErdosProblems1066.PachToth.ExplicitMetricRowsInhabitationW32
import ErdosProblems1066.PachToth.GeneratedMetricSourceFieldsW31

set_option autoImplicit false

/-!
# W32 concrete completion-row payloads

This file strengthens the W31 inhabitation layer by naming the concrete
payload rows carried by a generated completion source.  The constructors only
project or repackage W30/W31 completion-row and generated-metric source data.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CompletionRowsConcretePayloadsW32

noncomputable section

/-! ## Source vocabulary -/

abbrev GeneratedOrbitSkeleton : Type :=
  CompletionRowsInhabitationW31.GeneratedOrbitSkeleton

abbrev GeneratedClosureMetricRowPackage : Type :=
  CompletionRowsInhabitationW31.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  CompletionRowsInhabitationW31.GeneratedClosureMetricGate

abbrev DisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsInhabitationW31.DisplacementClosureRows G

abbrev SeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsInhabitationW31.SeparationRows G

abbrev SameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsInhabitationW31.SameBlockUnitRows G

abbrev CompletionRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsInhabitationW31.CompletionRows G

abbrev GeneratedCompletionRowsGate
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsInhabitationW31.GeneratedCompletionRowsGate G

abbrev AnyGeneratedCompletionRowsGate : Prop :=
  CompletionRowsInhabitationW31.AnyGeneratedCompletionRowsGate

abbrev SquaredOrbitClosureSourceRows : Type :=
  CompletionRowsInhabitationW31.SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  CompletionRowsInhabitationW31.SquaredOrbitClosureSourceRowsGate

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  CompletionRowsInhabitationW31.SquaredMinimalFieldsWithOrbitClosure

abbrev PointFamily : Type :=
  ClosedPlacementConcreteConstructionW27.PointFamily

abbrev StepFamily : Type :=
  ClosedPlacementConcreteConstructionW27.StepFamily

abbrev SquaredMetricClosureRows
    (point : PointFamily) (step : StepFamily) : Prop :=
  ClosedPlacementConcreteConstructionW27.SquaredMetricClosureRows point step

abbrev ConcreteClosedOrbitFamily : Type :=
  CompletionRowsInhabitationW31.ConcreteClosedOrbitFamily

abbrev MinimalFreePlacementFields : Type :=
  CompletionRowsInhabitationW31.MinimalFreePlacementFields

abbrev GeneratedCompletionRowData
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsInhabitationW31.GeneratedCompletionRowData G

abbrev GeneratedCompletionRowSource : Type :=
  CompletionRowsInhabitationW31.GeneratedCompletionRowSource

abbrev GeneratedMetricCompletionRowData : Type :=
  CompletionRowsInhabitationW31.GeneratedMetricCompletionRowData

abbrev GeneratedClosureCompletionRowsSource : Type :=
  CompletionRowsInhabitationW31.GeneratedClosureCompletionRowsSource

abbrev ExplicitGeneratedMetricSourceRows : Type :=
  GeneratedMetricSourceFieldsW31.ExplicitGeneratedMetricSourceRows

abbrev ExplicitPeriodMetricSourceRows : Type :=
  GeneratedMetricSourceFieldsW31.ExplicitPeriodMetricSourceRows

abbrev ExplicitClosureMetricRowPackage : Type :=
  ExplicitMetricRowsInhabitationW32.ExplicitClosureMetricRowPackage

abbrev ExplicitPeriodClosureMetricRowPackage : Type :=
  ExplicitMetricRowsInhabitationW32.ExplicitPeriodClosureMetricRowPackage

abbrev ExplicitClosureMetricFieldRows : Prop :=
  GeneratedMetricSourceFieldsW31.ExplicitClosureMetricFieldRows

abbrev GeneratedChainFamily : Type :=
  GeneratedMetricSourceFieldsW31.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.GeneratedChainFamilyClosures F

abbrev SeparationField
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.SeparationField F

abbrev BaseSameBlockField
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.BaseSameBlockField F

abbrev TransitionSameBlockField
    (F : GeneratedChainFamily) : Prop :=
  GeneratedMetricSourceFieldsW31.TransitionSameBlockField F

/-! ## Fixed-skeleton payload rows -/

/-- The three concrete row payloads needed by generated completion rows for a
fixed skeleton. -/
structure CompletionRowPayloads
    (G : GeneratedOrbitSkeleton) where
  displacement_closure : DisplacementClosureRows G
  separated_sq : SeparationRows G
  same_block_edges_sq_unit : SameBlockUnitRows G

namespace CompletionRowPayloads

def toW31Data
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    GeneratedCompletionRowData G where
  closure := P.displacement_closure
  separated_sq := P.separated_sq
  same_block_edges_sq_unit := P.same_block_edges_sq_unit

def ofW31Data
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    CompletionRowPayloads G where
  displacement_closure := D.closure
  separated_sq := D.separated_sq
  same_block_edges_sq_unit := D.same_block_edges_sq_unit

def toCompletionRows
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    CompletionRows G :=
  P.toW31Data.toCompletionRows

def ofCompletionRows
    {G : GeneratedOrbitSkeleton}
    (R : CompletionRows G) :
    CompletionRowPayloads G :=
  ofW31Data
    (CompletionRowsInhabitationW31.GeneratedCompletionRowData.ofCompletionRows
      R)

def toSourceRows
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    SquaredOrbitClosureSourceRows :=
  P.toW31Data.toSourceRows

def toSquaredMinimalFieldsWithOrbitClosure
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    SquaredMinimalFieldsWithOrbitClosure :=
  P.toW31Data.toSquaredMinimalFieldsWithOrbitClosure

def toSquaredMetricClosureRows
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    SquaredMetricClosureRows G.point G.step :=
  P.toSquaredMinimalFieldsWithOrbitClosure.toSquaredMetricClosureRows

def toConcreteClosedOrbitFamily
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    ConcreteClosedOrbitFamily :=
  P.toW31Data.toConcreteClosedOrbitFamily

def toMinimalFreePlacementFields
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    MinimalFreePlacementFields :=
  P.toW31Data.toMinimalFreePlacementFields

@[simp]
theorem toW31Data_closure
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    P.toW31Data.closure = P.displacement_closure :=
  rfl

@[simp]
theorem toW31Data_separated_sq
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    P.toW31Data.separated_sq = P.separated_sq :=
  rfl

@[simp]
theorem toW31Data_same_block_edges_sq_unit
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    P.toW31Data.same_block_edges_sq_unit =
      P.same_block_edges_sq_unit :=
  rfl

@[simp]
theorem ofW31Data_displacement_closure
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    (ofW31Data D).displacement_closure = D.closure :=
  rfl

@[simp]
theorem ofW31Data_separated_sq
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    (ofW31Data D).separated_sq = D.separated_sq :=
  rfl

@[simp]
theorem ofW31Data_same_block_edges_sq_unit
    {G : GeneratedOrbitSkeleton}
    (D : GeneratedCompletionRowData G) :
    (ofW31Data D).same_block_edges_sq_unit =
      D.same_block_edges_sq_unit :=
  rfl

@[simp]
theorem toSourceRows_skeleton
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    P.toSourceRows.skeleton = G :=
  CompletionRowsInhabitationW31.GeneratedCompletionRowData.toSourceRows_skeleton
    P.toW31Data

end CompletionRowPayloads

def completionRowPayloadsOfCompletionRows
    {G : GeneratedOrbitSkeleton}
    (R : CompletionRows G) :
    CompletionRowPayloads G :=
  CompletionRowPayloads.ofCompletionRows R

def completionRowPayloadsOfSourceRows
    (S : SquaredOrbitClosureSourceRows) :
    CompletionRowPayloads S.skeleton :=
  CompletionRowPayloads.ofCompletionRows S.rows

@[simp]
theorem completionRowPayloadsOfSourceRows_displacement_closure
    (S : SquaredOrbitClosureSourceRows) :
    (completionRowPayloadsOfSourceRows S).displacement_closure =
      S.rows.closure :=
  rfl

@[simp]
theorem completionRowPayloadsOfSourceRows_separated_sq
    (S : SquaredOrbitClosureSourceRows) :
    (completionRowPayloadsOfSourceRows S).separated_sq =
      S.rows.separated_sq :=
  rfl

@[simp]
theorem completionRowPayloadsOfSourceRows_same_block_edges_sq_unit
    (S : SquaredOrbitClosureSourceRows) :
    (completionRowPayloadsOfSourceRows S).same_block_edges_sq_unit =
      S.rows.same_block_edges_sq_unit :=
  rfl

def displacementClosureRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    DisplacementClosureRows
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        P) :=
  CompletionRowsSourceW29.displacementClosureRowsOfGeneratedClosureMetricRowPackage
    P

def separationRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    SeparationRows
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        P) :=
  CompletionRowsSourceW29.separationRowsOfGeneratedClosureMetricRowPackage
    P

def sameBlockUnitRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    SameBlockUnitRows
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        P) :=
  CompletionRowsSourceW29.sameBlockUnitRowsOfGeneratedClosureMetricRowPackage
    P

def completionRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    CompletionRows
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        P) where
  closure := displacementClosureRowsOfGeneratedClosureMetricRowPackage P
  separated_sq := separationRowsOfGeneratedClosureMetricRowPackage P
  same_block_edges_sq_unit :=
    sameBlockUnitRowsOfGeneratedClosureMetricRowPackage P

def completionRowPayloadsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    CompletionRowPayloads
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        P) :=
  { displacement_closure :=
      displacementClosureRowsOfGeneratedClosureMetricRowPackage P
    separated_sq := separationRowsOfGeneratedClosureMetricRowPackage P
    same_block_edges_sq_unit :=
      sameBlockUnitRowsOfGeneratedClosureMetricRowPackage P }

@[simp]
theorem completionRowsOfGeneratedClosureMetricRowPackage_closure
    (P : GeneratedClosureMetricRowPackage) :
    (completionRowsOfGeneratedClosureMetricRowPackage P).closure =
      displacementClosureRowsOfGeneratedClosureMetricRowPackage P :=
  rfl

@[simp]
theorem completionRowsOfGeneratedClosureMetricRowPackage_separated_sq
    (P : GeneratedClosureMetricRowPackage) :
    (completionRowsOfGeneratedClosureMetricRowPackage P).separated_sq =
      separationRowsOfGeneratedClosureMetricRowPackage P :=
  rfl

@[simp]
theorem completionRowsOfGeneratedClosureMetricRowPackage_same_block_edges_sq_unit
    (P : GeneratedClosureMetricRowPackage) :
    (completionRowsOfGeneratedClosureMetricRowPackage P).same_block_edges_sq_unit =
      sameBlockUnitRowsOfGeneratedClosureMetricRowPackage P :=
  rfl

@[simp]
theorem completionRowPayloadsOfGeneratedClosureMetricRowPackage_displacement_closure
    (P : GeneratedClosureMetricRowPackage) :
    (completionRowPayloadsOfGeneratedClosureMetricRowPackage
      P).displacement_closure =
      displacementClosureRowsOfGeneratedClosureMetricRowPackage P :=
  rfl

@[simp]
theorem completionRowPayloadsOfGeneratedClosureMetricRowPackage_separated_sq
    (P : GeneratedClosureMetricRowPackage) :
    (completionRowPayloadsOfGeneratedClosureMetricRowPackage
      P).separated_sq =
      separationRowsOfGeneratedClosureMetricRowPackage P :=
  rfl

@[simp]
theorem completionRowPayloadsOfGeneratedClosureMetricRowPackage_same_block_edges_sq_unit
    (P : GeneratedClosureMetricRowPackage) :
    (completionRowPayloadsOfGeneratedClosureMetricRowPackage
      P).same_block_edges_sq_unit =
      sameBlockUnitRowsOfGeneratedClosureMetricRowPackage P :=
  rfl

theorem source_rows_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    DisplacementClosureRows
        (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
          P) /\
      SeparationRows
        (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
          P) /\
        SameBlockUnitRows
          (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
            P) :=
  And.intro
    (displacementClosureRowsOfGeneratedClosureMetricRowPackage P)
    (And.intro
      (separationRowsOfGeneratedClosureMetricRowPackage P)
      (sameBlockUnitRowsOfGeneratedClosureMetricRowPackage P))

theorem nonempty_completionRowPayloads_of_sourceRows
    (S : SquaredOrbitClosureSourceRows) :
    Nonempty (CompletionRowPayloads S.skeleton) :=
  Nonempty.intro (completionRowPayloadsOfSourceRows S)

theorem nonempty_completionRowPayloads_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    Nonempty
      (CompletionRowPayloads
        (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
          P)) :=
  Nonempty.intro
    (completionRowPayloadsOfGeneratedClosureMetricRowPackage P)

theorem exists_completionRowPayloads_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    Exists fun G : GeneratedOrbitSkeleton =>
      Nonempty (CompletionRowPayloads G) := by
  cases H with
  | intro P =>
      exact
        Exists.intro
          (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
            P)
          (nonempty_completionRowPayloads_of_generatedClosureMetricRowPackage
            P)

theorem nonempty_completionRowPayloads_iff_w31Data
    (G : GeneratedOrbitSkeleton) :
    Nonempty (CompletionRowPayloads G) <->
      Nonempty (GeneratedCompletionRowData G) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toW31Data
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro (CompletionRowPayloads.ofW31Data D)

theorem nonempty_completionRowPayloads_iff_completionRowsGate
    (G : GeneratedOrbitSkeleton) :
    Nonempty (CompletionRowPayloads G) <->
      GeneratedCompletionRowsGate G :=
  Iff.trans (nonempty_completionRowPayloads_iff_w31Data G)
    (CompletionRowsInhabitationW31.nonempty_generatedCompletionRowData_iff_completionRowsGate
      G)

theorem nonempty_completionRowPayloads_iff_source_rows
    (G : GeneratedOrbitSkeleton) :
    Nonempty (CompletionRowPayloads G) <->
      DisplacementClosureRows G /\
        SeparationRows G /\
          SameBlockUnitRows G := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          And.intro P.displacement_closure
            (And.intro P.separated_sq P.same_block_edges_sq_unit)
  case mpr =>
    intro h
    exact
      Nonempty.intro
        { displacement_closure := h.1
          separated_sq := h.2.1
          same_block_edges_sq_unit := h.2.2 }

theorem exists_squaredMetricClosureRows_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    Exists fun point : PointFamily =>
      Exists fun step : StepFamily =>
        SquaredMetricClosureRows point step := by
  exact Exists.intro G.point
    (Exists.intro G.step P.toSquaredMetricClosureRows)

theorem nonempty_concreteClosedOrbitFamily_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    Nonempty ConcreteClosedOrbitFamily :=
  Nonempty.intro P.toConcreteClosedOrbitFamily

/-! ## Source records over arbitrary generated skeletons -/

/-- A generated skeleton paired with its concrete completion payload rows. -/
structure CompletionPayloadSource where
  skeleton : GeneratedOrbitSkeleton
  payloads : CompletionRowPayloads skeleton

namespace CompletionPayloadSource

def toW31Source
    (S : CompletionPayloadSource) :
    GeneratedCompletionRowSource where
  skeleton := S.skeleton
  data := S.payloads.toW31Data

def ofW31Source
    (S : GeneratedCompletionRowSource) :
    CompletionPayloadSource where
  skeleton := S.skeleton
  payloads := CompletionRowPayloads.ofW31Data S.data

def ofSourceRows
    (S : SquaredOrbitClosureSourceRows) :
    CompletionPayloadSource where
  skeleton := S.skeleton
  payloads := CompletionRowPayloads.ofCompletionRows S.rows

def toCompletionRows
    (S : CompletionPayloadSource) :
    CompletionRows S.skeleton :=
  S.payloads.toCompletionRows

def toSourceRows
    (S : CompletionPayloadSource) :
    SquaredOrbitClosureSourceRows :=
  S.payloads.toSourceRows

def toSquaredMinimalFieldsWithOrbitClosure
    (S : CompletionPayloadSource) :
    SquaredMinimalFieldsWithOrbitClosure :=
  S.payloads.toSquaredMinimalFieldsWithOrbitClosure

def toSquaredMetricClosureRows
    (S : CompletionPayloadSource) :
    SquaredMetricClosureRows S.skeleton.point S.skeleton.step :=
  S.payloads.toSquaredMetricClosureRows

def toConcreteClosedOrbitFamily
    (S : CompletionPayloadSource) :
    ConcreteClosedOrbitFamily :=
  S.payloads.toConcreteClosedOrbitFamily

def toMinimalFreePlacementFields
    (S : CompletionPayloadSource) :
    MinimalFreePlacementFields :=
  S.payloads.toMinimalFreePlacementFields

@[simp]
theorem toW31Source_skeleton
    (S : CompletionPayloadSource) :
    S.toW31Source.skeleton = S.skeleton :=
  rfl

@[simp]
theorem ofW31Source_skeleton
    (S : GeneratedCompletionRowSource) :
    (ofW31Source S).skeleton = S.skeleton :=
  rfl

@[simp]
theorem ofSourceRows_skeleton
    (S : SquaredOrbitClosureSourceRows) :
    (ofSourceRows S).skeleton = S.skeleton :=
  rfl

@[simp]
theorem toSourceRows_skeleton
    (S : CompletionPayloadSource) :
    S.toSourceRows.skeleton = S.skeleton :=
  CompletionRowPayloads.toSourceRows_skeleton S.payloads

end CompletionPayloadSource

def completionPayloadSourceOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    CompletionPayloadSource where
  skeleton :=
    CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage P
  payloads := completionRowPayloadsOfGeneratedClosureMetricRowPackage P

def completionPayloadSourceOfGeneratedClosureCompletionRowsSource
    (S : GeneratedClosureCompletionRowsSource) :
    CompletionPayloadSource where
  skeleton :=
    CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
      S.package
  payloads := CompletionRowPayloads.ofCompletionRows S.rows

def completionPayloadSourceOfExplicitGeneratedMetricSourceRows
    (R : ExplicitGeneratedMetricSourceRows) :
    CompletionPayloadSource :=
  completionPayloadSourceOfGeneratedClosureMetricRowPackage
    R.toGeneratedClosureMetricRowPackage

def completionPayloadSourceOfExplicitPeriodMetricSourceRows
    (R : ExplicitPeriodMetricSourceRows) :
    CompletionPayloadSource :=
  completionPayloadSourceOfGeneratedClosureMetricRowPackage
    R.toGeneratedClosureMetricRowPackage

def generatedClosureMetricRowPackageOfExplicitGeneratedMetricSourceRows
    (R : ExplicitGeneratedMetricSourceRows) :
    GeneratedClosureMetricRowPackage :=
  GeneratedMetricSourceFieldsW31.generatedClosureMetricRowPackageOfExplicitGeneratedMetricSourceRows
    R

def sourceRowsOfExplicitGeneratedMetricSourceRows
    (R : ExplicitGeneratedMetricSourceRows) :
    SquaredOrbitClosureSourceRows :=
  GeneratedMetricSourceFieldsW31.squaredOrbitClosureSourceRowsOfExplicitGeneratedMetricSourceRows
    R

def generatedClosureMetricRowPackageOfExplicitClosureMetricRowPackage
    (S : ExplicitClosureMetricRowPackage) :
    GeneratedClosureMetricRowPackage :=
  ExplicitMetricRowsInhabitationW32.generatedClosureMetricRowPackageOfExplicitClosureMetricRowPackage
    S

def sourceRowsOfExplicitClosureMetricRowPackage
    (S : ExplicitClosureMetricRowPackage) :
    SquaredOrbitClosureSourceRows :=
  ExplicitMetricRowsInhabitationW32.squaredOrbitClosureSourceRowsOfExplicitClosureMetricRowPackage
    S

def completionPayloadSourceOfExplicitClosureMetricRowPackage
    (S : ExplicitClosureMetricRowPackage) :
    CompletionPayloadSource :=
  completionPayloadSourceOfGeneratedClosureMetricRowPackage
    (generatedClosureMetricRowPackageOfExplicitClosureMetricRowPackage S)

def completionPayloadSourceOfExplicitPeriodClosureMetricRowPackage
    (S : ExplicitPeriodClosureMetricRowPackage) :
    CompletionPayloadSource :=
  completionPayloadSourceOfExplicitPeriodMetricSourceRows
    S.toExplicitPeriodMetricSourceRows

def completionRowPayloadsOfExplicitGeneratedMetricSourceRows
    (R : ExplicitGeneratedMetricSourceRows) :
    CompletionRowPayloads
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        R.toGeneratedClosureMetricRowPackage) :=
  completionRowPayloadsOfGeneratedClosureMetricRowPackage
    R.toGeneratedClosureMetricRowPackage

def completionRowPayloadsOfExplicitPeriodMetricSourceRows
    (R : ExplicitPeriodMetricSourceRows) :
    CompletionRowPayloads
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        R.toGeneratedClosureMetricRowPackage) :=
  completionRowPayloadsOfGeneratedClosureMetricRowPackage
    R.toGeneratedClosureMetricRowPackage

def completionRowPayloadsOfExplicitClosureMetricRowPackage
    (S : ExplicitClosureMetricRowPackage) :
    CompletionRowPayloads
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        S.toGeneratedClosureMetricRowPackage) :=
  completionRowPayloadsOfGeneratedClosureMetricRowPackage
    S.toGeneratedClosureMetricRowPackage

def completionRowPayloadsOfExplicitPeriodClosureMetricRowPackage
    (S : ExplicitPeriodClosureMetricRowPackage) :
    CompletionRowPayloads
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        S.toGeneratedClosureMetricRowPackage) :=
  completionRowPayloadsOfGeneratedClosureMetricRowPackage
    S.toGeneratedClosureMetricRowPackage

theorem nonempty_completionPayloadSource_iff_w31Source :
    Nonempty CompletionPayloadSource <->
      Nonempty GeneratedCompletionRowSource := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toW31Source
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro (CompletionPayloadSource.ofW31Source S)

theorem nonempty_completionPayloadSource_iff_sourceRowsGate :
    Nonempty CompletionPayloadSource <->
      SquaredOrbitClosureSourceRowsGate :=
  Iff.trans nonempty_completionPayloadSource_iff_w31Source
    CompletionRowsInhabitationW31.nonempty_generatedCompletionRowSource_iff_sourceRowsGate

theorem nonempty_completionPayloadSource_iff_anyCompletionRowsGate :
    Nonempty CompletionPayloadSource <->
      AnyGeneratedCompletionRowsGate :=
  Iff.trans nonempty_completionPayloadSource_iff_w31Source
    CompletionRowsInhabitationW31.nonempty_generatedCompletionRowSource_iff_anyCompletionRowsGate

theorem completionPayloadSource_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    Nonempty CompletionPayloadSource := by
  cases H with
  | intro P =>
      exact
        Nonempty.intro
          (completionPayloadSourceOfGeneratedClosureMetricRowPackage P)

theorem completionPayloadSource_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    Nonempty CompletionPayloadSource :=
  nonempty_completionPayloadSource_iff_sourceRowsGate.mpr H

theorem completionPayloadSource_of_explicitGeneratedMetricSourceRows
    (H : Nonempty ExplicitGeneratedMetricSourceRows) :
    Nonempty CompletionPayloadSource := by
  cases H with
  | intro R =>
      exact
        Nonempty.intro
          (completionPayloadSourceOfExplicitGeneratedMetricSourceRows R)

theorem generatedClosureMetricGate_of_explicitGeneratedMetricSourceRows
    (H : Nonempty ExplicitGeneratedMetricSourceRows) :
    GeneratedClosureMetricGate := by
  cases H with
  | intro R =>
      exact
        Nonempty.intro
          (generatedClosureMetricRowPackageOfExplicitGeneratedMetricSourceRows
            R)

theorem sourceRowsGate_of_explicitGeneratedMetricSourceRows
    (H : Nonempty ExplicitGeneratedMetricSourceRows) :
    SquaredOrbitClosureSourceRowsGate := by
  cases H with
  | intro R =>
      exact Nonempty.intro (sourceRowsOfExplicitGeneratedMetricSourceRows R)

theorem completionPayloadSource_of_explicitClosureMetricRowPackage
    (H : Nonempty ExplicitClosureMetricRowPackage) :
    Nonempty CompletionPayloadSource := by
  cases H with
  | intro S =>
      exact
        Nonempty.intro
          (completionPayloadSourceOfExplicitClosureMetricRowPackage S)

theorem generatedClosureMetricGate_of_explicitClosureMetricRowPackage
    (H : Nonempty ExplicitClosureMetricRowPackage) :
    GeneratedClosureMetricGate := by
  cases H with
  | intro S =>
      exact
        Nonempty.intro
          (generatedClosureMetricRowPackageOfExplicitClosureMetricRowPackage
            S)

theorem sourceRowsGate_of_explicitClosureMetricRowPackage
    (H : Nonempty ExplicitClosureMetricRowPackage) :
    SquaredOrbitClosureSourceRowsGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro (sourceRowsOfExplicitClosureMetricRowPackage S)

theorem completionPayloadSource_of_explicitPeriodClosureMetricRowPackage
    (H : Nonempty ExplicitPeriodClosureMetricRowPackage) :
    Nonempty CompletionPayloadSource := by
  cases H with
  | intro S =>
      exact
        Nonempty.intro
          (completionPayloadSourceOfExplicitPeriodClosureMetricRowPackage S)

theorem completionPayloadSource_of_explicitPeriodMetricSourceRows
    (H : Nonempty ExplicitPeriodMetricSourceRows) :
    Nonempty CompletionPayloadSource := by
  cases H with
  | intro R =>
      exact
        Nonempty.intro
          (completionPayloadSourceOfExplicitPeriodMetricSourceRows R)

theorem exists_completionRowPayloads_of_explicitGeneratedMetricSourceRows
    (H : Nonempty ExplicitGeneratedMetricSourceRows) :
    Exists fun G : GeneratedOrbitSkeleton =>
      Nonempty (CompletionRowPayloads G) := by
  cases H with
  | intro R =>
      exact
        Exists.intro
          (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
            R.toGeneratedClosureMetricRowPackage)
          (Nonempty.intro
            (completionRowPayloadsOfExplicitGeneratedMetricSourceRows R))

theorem exists_completionRowPayloads_of_explicitPeriodMetricSourceRows
    (H : Nonempty ExplicitPeriodMetricSourceRows) :
    Exists fun G : GeneratedOrbitSkeleton =>
      Nonempty (CompletionRowPayloads G) := by
  cases H with
  | intro R =>
      exact
        Exists.intro
          (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
            R.toGeneratedClosureMetricRowPackage)
          (Nonempty.intro
            (completionRowPayloadsOfExplicitPeriodMetricSourceRows R))

theorem exists_completionRowPayloads_of_explicitClosureMetricRowPackage
    (H : Nonempty ExplicitClosureMetricRowPackage) :
    Exists fun G : GeneratedOrbitSkeleton =>
      Nonempty (CompletionRowPayloads G) := by
  cases H with
  | intro S =>
      exact
        Exists.intro
          (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
            S.toGeneratedClosureMetricRowPackage)
          (Nonempty.intro
            (completionRowPayloadsOfExplicitClosureMetricRowPackage S))

theorem exists_completionRowPayloads_of_explicitPeriodClosureMetricRowPackage
    (H : Nonempty ExplicitPeriodClosureMetricRowPackage) :
    Exists fun G : GeneratedOrbitSkeleton =>
      Nonempty (CompletionRowPayloads G) := by
  cases H with
  | intro S =>
      exact
        Exists.intro
          (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
            S.toGeneratedClosureMetricRowPackage)
          (Nonempty.intro
            (completionRowPayloadsOfExplicitPeriodClosureMetricRowPackage S))

theorem exists_squaredMetricClosureRows_of_completionPayloadSource
    (S : CompletionPayloadSource) :
    Exists fun point : PointFamily =>
      Exists fun step : StepFamily =>
        SquaredMetricClosureRows point step :=
  exists_squaredMetricClosureRows_of_completionRowPayloads S.payloads

theorem exists_squaredMetricClosureRows_of_completionPayloadSourceGate
    (H : Nonempty CompletionPayloadSource) :
    Exists fun point : PointFamily =>
      Exists fun step : StepFamily =>
        SquaredMetricClosureRows point step := by
  cases H with
  | intro S =>
      exact exists_squaredMetricClosureRows_of_completionPayloadSource S

theorem nonempty_concreteClosedOrbitFamily_of_completionPayloadSource
    (S : CompletionPayloadSource) :
    Nonempty ConcreteClosedOrbitFamily :=
  Nonempty.intro S.toConcreteClosedOrbitFamily

theorem nonempty_concreteClosedOrbitFamily_of_completionPayloadSourceGate
    (H : Nonempty CompletionPayloadSource) :
    Nonempty ConcreteClosedOrbitFamily := by
  cases H with
  | intro S =>
      exact nonempty_concreteClosedOrbitFamily_of_completionPayloadSource S

/-! ## Generated-metric packages carrying payload rows -/

/-- A generated-metric source package with the concrete completion payloads
for its induced generated skeleton. -/
structure GeneratedMetricCompletionPayloads where
  package : GeneratedClosureMetricRowPackage
  payloads :
    CompletionRowPayloads
      (CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        package)

namespace GeneratedMetricCompletionPayloads

def ofPackage
    (P : GeneratedClosureMetricRowPackage) :
    GeneratedMetricCompletionPayloads where
  package := P
  payloads := completionRowPayloadsOfGeneratedClosureMetricRowPackage P

def toW31Data
    (S : GeneratedMetricCompletionPayloads) :
    GeneratedMetricCompletionRowData where
  package := S.package
  data := S.payloads.toW31Data

def ofW31Data
    (S : GeneratedMetricCompletionRowData) :
    GeneratedMetricCompletionPayloads where
  package := S.package
  payloads := CompletionRowPayloads.ofW31Data S.data

def toW30Source
    (S : GeneratedMetricCompletionPayloads) :
    GeneratedClosureCompletionRowsSource where
  package := S.package
  rows := S.payloads.toCompletionRows

def ofW30Source
    (S : GeneratedClosureCompletionRowsSource) :
    GeneratedMetricCompletionPayloads where
  package := S.package
  payloads := CompletionRowPayloads.ofCompletionRows S.rows

def toCompletionPayloadSource
    (S : GeneratedMetricCompletionPayloads) :
    CompletionPayloadSource where
  skeleton :=
    CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
      S.package
  payloads := S.payloads

def ofExplicitGeneratedMetricSourceRows
    (R : ExplicitGeneratedMetricSourceRows) :
    GeneratedMetricCompletionPayloads :=
  ofPackage R.toGeneratedClosureMetricRowPackage

def ofExplicitPeriodMetricSourceRows
    (R : ExplicitPeriodMetricSourceRows) :
    GeneratedMetricCompletionPayloads :=
  ofPackage R.toGeneratedClosureMetricRowPackage

@[simp]
theorem ofPackage_package
    (P : GeneratedClosureMetricRowPackage) :
    (ofPackage P).package = P :=
  rfl

@[simp]
theorem toW31Data_package
    (S : GeneratedMetricCompletionPayloads) :
    S.toW31Data.package = S.package :=
  rfl

@[simp]
theorem ofW31Data_package
    (S : GeneratedMetricCompletionRowData) :
    (ofW31Data S).package = S.package :=
  rfl

@[simp]
theorem toW30Source_package
    (S : GeneratedMetricCompletionPayloads) :
    S.toW30Source.package = S.package :=
  rfl

@[simp]
theorem ofW30Source_package
    (S : GeneratedClosureCompletionRowsSource) :
    (ofW30Source S).package = S.package :=
  rfl

@[simp]
theorem toCompletionPayloadSource_skeleton
    (S : GeneratedMetricCompletionPayloads) :
    S.toCompletionPayloadSource.skeleton =
      CompletionRowsClosureW30.skeletonOfGeneratedClosureMetricRowPackage
        S.package :=
  rfl

end GeneratedMetricCompletionPayloads

theorem nonempty_generatedMetricCompletionPayloads_iff_w31Data :
    Nonempty GeneratedMetricCompletionPayloads <->
      Nonempty GeneratedMetricCompletionRowData := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toW31Data
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro
          (GeneratedMetricCompletionPayloads.ofW31Data S)

theorem nonempty_generatedMetricCompletionPayloads_iff_w30Source :
    Nonempty GeneratedMetricCompletionPayloads <->
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
        exact Nonempty.intro
          (GeneratedMetricCompletionPayloads.ofW30Source S)

theorem nonempty_generatedMetricCompletionPayloads_iff_generatedClosureMetricGate :
    Nonempty GeneratedMetricCompletionPayloads <->
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
        exact Nonempty.intro
          (GeneratedMetricCompletionPayloads.ofPackage P)

theorem nonempty_generatedMetricCompletionPayloads_iff_explicitGeneratedMetricSourceRows :
    Nonempty GeneratedMetricCompletionPayloads <->
      Nonempty ExplicitGeneratedMetricSourceRows :=
  Iff.trans
    nonempty_generatedMetricCompletionPayloads_iff_generatedClosureMetricGate
    GeneratedMetricSourceFieldsW31.explicitGeneratedMetricSourceRows_iff_generatedClosureMetricGate.symm

theorem nonempty_generatedMetricCompletionPayloads_iff_explicitFieldRows :
    Nonempty GeneratedMetricCompletionPayloads <->
      ExplicitClosureMetricFieldRows :=
  Iff.trans
    nonempty_generatedMetricCompletionPayloads_iff_generatedClosureMetricGate
    GeneratedMetricSourceFieldsW31.generatedClosureMetricGate_iff_explicitFieldRows

theorem generatedMetricCompletionPayloads_of_explicitPeriodMetricSourceRows
    (H : Nonempty ExplicitPeriodMetricSourceRows) :
    Nonempty GeneratedMetricCompletionPayloads := by
  cases H with
  | intro R =>
      exact
        Nonempty.intro
          (GeneratedMetricCompletionPayloads.ofExplicitPeriodMetricSourceRows
            R)

theorem generatedMetricCompletionPayloads_of_explicitGeneratedMetricSourceRows
    (H : Nonempty ExplicitGeneratedMetricSourceRows) :
    Nonempty GeneratedMetricCompletionPayloads := by
  cases H with
  | intro R =>
      exact
        Nonempty.intro
          (GeneratedMetricCompletionPayloads.ofExplicitGeneratedMetricSourceRows
            R)

theorem completionPayloadSource_of_generatedMetricCompletionPayloads
    (H : Nonempty GeneratedMetricCompletionPayloads) :
    Nonempty CompletionPayloadSource := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.toCompletionPayloadSource

theorem exists_squaredMetricClosureRows_of_generatedMetricCompletionPayloads
    (S : GeneratedMetricCompletionPayloads) :
    Exists fun point : PointFamily =>
      Exists fun step : StepFamily =>
        SquaredMetricClosureRows point step :=
  exists_squaredMetricClosureRows_of_completionRowPayloads S.payloads

theorem nonempty_concreteClosedOrbitFamily_of_generatedMetricCompletionPayloads
    (S : GeneratedMetricCompletionPayloads) :
    Nonempty ConcreteClosedOrbitFamily :=
  nonempty_concreteClosedOrbitFamily_of_completionRowPayloads S.payloads

/-! ## Compact certificate -/

abbrev CompletionPayloadsCertificate : Prop :=
  (forall G : GeneratedOrbitSkeleton,
    Nonempty (CompletionRowPayloads G) <->
      GeneratedCompletionRowsGate G) /\
    (Nonempty CompletionPayloadSource <->
      SquaredOrbitClosureSourceRowsGate) /\
      (Nonempty GeneratedMetricCompletionPayloads <->
        GeneratedClosureMetricGate) /\
        (Nonempty GeneratedMetricCompletionPayloads <->
          ExplicitClosureMetricFieldRows)

theorem completionPayloadsCertificate :
    CompletionPayloadsCertificate :=
  And.intro nonempty_completionRowPayloads_iff_completionRowsGate
    (And.intro nonempty_completionPayloadSource_iff_sourceRowsGate
      (And.intro
        nonempty_generatedMetricCompletionPayloads_iff_generatedClosureMetricGate
        nonempty_generatedMetricCompletionPayloads_iff_explicitFieldRows))

abbrev W27ClosedOrbitPayloadBridgeCertificate : Prop :=
  (forall G : GeneratedOrbitSkeleton,
    CompletionRowPayloads G ->
      SquaredMetricClosureRows G.point G.step) /\
    (Nonempty CompletionPayloadSource ->
      Nonempty ConcreteClosedOrbitFamily) /\
      (forall G : GeneratedOrbitSkeleton,
        Nonempty (CompletionRowPayloads G) <->
          DisplacementClosureRows G /\
            SeparationRows G /\
              SameBlockUnitRows G)

theorem w27ClosedOrbitPayloadBridgeCertificate :
    W27ClosedOrbitPayloadBridgeCertificate :=
  And.intro
    (fun _G P => P.toSquaredMetricClosureRows)
    (And.intro
      nonempty_concreteClosedOrbitFamily_of_completionPayloadSourceGate
      nonempty_completionRowPayloads_iff_source_rows)

end

end CompletionRowsConcretePayloadsW32
end PachToth

namespace Verified

abbrev PachTothW32CompletionRowPayloads
    (G :
      PachToth.CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton) :
    Prop :=
  PachToth.CompletionRowsConcretePayloadsW32.CompletionRowPayloads G

abbrev PachTothW32CompletionPayloadSource : Type :=
  PachToth.CompletionRowsConcretePayloadsW32.CompletionPayloadSource

abbrev PachTothW32GeneratedMetricCompletionPayloads : Type :=
  PachToth.CompletionRowsConcretePayloadsW32.GeneratedMetricCompletionPayloads

abbrev PachTothW32ExplicitClosureMetricFieldRows : Prop :=
  PachToth.CompletionRowsConcretePayloadsW32.ExplicitClosureMetricFieldRows

abbrev PachTothW32W27ClosedOrbitPayloadBridgeCertificate : Prop :=
  PachToth.CompletionRowsConcretePayloadsW32.W27ClosedOrbitPayloadBridgeCertificate

theorem pachtoth_w32_completionRowPayloads_iff_completionRowsGate
    (G :
      PachToth.CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton) :
    Nonempty (PachTothW32CompletionRowPayloads G) <->
      PachToth.CompletionRowsConcretePayloadsW32.GeneratedCompletionRowsGate
        G :=
  PachToth.CompletionRowsConcretePayloadsW32.nonempty_completionRowPayloads_iff_completionRowsGate
    G

theorem pachtoth_w32_completionPayloadSource_iff_sourceRowsGate :
    Nonempty PachTothW32CompletionPayloadSource <->
      PachToth.CompletionRowsConcretePayloadsW32.SquaredOrbitClosureSourceRowsGate :=
  PachToth.CompletionRowsConcretePayloadsW32.nonempty_completionPayloadSource_iff_sourceRowsGate

theorem pachtoth_w32_generatedMetricPayloads_iff_explicitFieldRows :
    Nonempty PachTothW32GeneratedMetricCompletionPayloads <->
      PachTothW32ExplicitClosureMetricFieldRows :=
  PachToth.CompletionRowsConcretePayloadsW32.nonempty_generatedMetricCompletionPayloads_iff_explicitFieldRows

theorem pachtoth_w32_completionPayloadsCertificate :
    PachToth.CompletionRowsConcretePayloadsW32.CompletionPayloadsCertificate :=
  PachToth.CompletionRowsConcretePayloadsW32.completionPayloadsCertificate

theorem pachtoth_w32_w27ClosedOrbitPayloadBridgeCertificate :
    PachTothW32W27ClosedOrbitPayloadBridgeCertificate :=
  PachToth.CompletionRowsConcretePayloadsW32.w27ClosedOrbitPayloadBridgeCertificate

end Verified
end ErdosProblems1066
