import ErdosProblems1066.PachToth.CompletionRowsSourceW29

set_option autoImplicit false

/-!
# W29 completion-row handoff into squared orbit closure

This file is the source-facing bridge from checked completion rows to the W28
squared-orbit closure route.  It consumes `CompletionRows`, or the three row
families that make one, and then forwards them to the W27
`SquaredMinimalFieldsWithOrbitClosure` and `ConcreteClosedOrbitFamily` gates.

No declaration below constructs row data from a closed-orbit target.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SquaredOrbitClosureCompletionRowsW29

noncomputable section

abbrev GeneratedOrbitSkeleton : Type :=
  SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton

abbrev DisplacementClosureRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton.DisplacementClosureRows G

abbrev SeparationRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton.SeparationRows G

abbrev SameBlockUnitRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton.SameBlockUnitRows G

abbrev CompletionRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton.CompletionRows G

abbrev SquaredOrbitClosureSourceRows : Type :=
  SquaredOrbitClosureSourceW28.SquaredOrbitClosureSourceRows

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  SquaredOrbitClosureSourceW28.SquaredMinimalFieldsWithOrbitClosure

abbrev ConcreteClosedOrbitFamily : Type :=
  SquaredOrbitClosureSourceW28.ConcreteClosedOrbitFamily

abbrev MinimalFreePlacementFields : Type :=
  SquaredOrbitClosureSourceW28.MinimalFreePlacementFields

abbrev GeneratedClosureMetricRowPackage : Type :=
  CompletionRowsSourceW29.GeneratedClosureMetricRowPackage

def completionRowsOfDisplacementClosureSeparation
    {G : GeneratedOrbitSkeleton}
    (closure : DisplacementClosureRows G)
    (separated_sq : SeparationRows G)
    (same_block_edges_sq_unit : SameBlockUnitRows G) :
    CompletionRows G where
  closure := closure
  separated_sq := separated_sq
  same_block_edges_sq_unit := same_block_edges_sq_unit

def sourceRowsOfCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : CompletionRows G) :
    SquaredOrbitClosureSourceRows where
  skeleton := G
  rows := R

def sourceRowsOfDisplacementClosureSeparation
    {G : GeneratedOrbitSkeleton}
    (closure : DisplacementClosureRows G)
    (separated_sq : SeparationRows G)
    (same_block_edges_sq_unit : SameBlockUnitRows G) :
    SquaredOrbitClosureSourceRows :=
  sourceRowsOfCompletionRows G
    (completionRowsOfDisplacementClosureSeparation
      closure separated_sq same_block_edges_sq_unit)

def completionRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    CompletionRows
      (CompletionRowsSourceW29.skeletonOfGeneratedClosureMetricRowPackage P) :=
  CompletionRowsSourceW29.completionRowsOfGeneratedClosureMetricRowPackage P

def sourceRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    SquaredOrbitClosureSourceRows :=
  CompletionRowsSourceW29.squaredOrbitClosureSourceRowsOfGeneratedClosureMetricRowPackage
    P

@[simp]
theorem sourceRowsOfCompletionRows_skeleton
    (G : GeneratedOrbitSkeleton)
    (R : CompletionRows G) :
    (sourceRowsOfCompletionRows G R).skeleton = G :=
  rfl

def squaredMinimalFieldsWithOrbitClosureOfCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : CompletionRows G) :
    SquaredMinimalFieldsWithOrbitClosure :=
  (sourceRowsOfCompletionRows G R).toSquaredMinimalFieldsWithOrbitClosure

def concreteClosedOrbitFamilyOfCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : CompletionRows G) :
    ConcreteClosedOrbitFamily :=
  (sourceRowsOfCompletionRows G R).toConcreteClosedOrbitFamily

def minimalFreePlacementFieldsOfCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : CompletionRows G) :
    MinimalFreePlacementFields :=
  (sourceRowsOfCompletionRows G R).toConcreteClosedOrbitFamily
    |>.toMinimalFreePlacementFields

def squaredMinimalFieldsWithOrbitClosureOfDisplacementClosureSeparation
    {G : GeneratedOrbitSkeleton}
    (closure : DisplacementClosureRows G)
    (separated_sq : SeparationRows G)
    (same_block_edges_sq_unit : SameBlockUnitRows G) :
    SquaredMinimalFieldsWithOrbitClosure :=
  (sourceRowsOfDisplacementClosureSeparation
    closure separated_sq same_block_edges_sq_unit)
      |>.toSquaredMinimalFieldsWithOrbitClosure

def concreteClosedOrbitFamilyOfDisplacementClosureSeparation
    {G : GeneratedOrbitSkeleton}
    (closure : DisplacementClosureRows G)
    (separated_sq : SeparationRows G)
    (same_block_edges_sq_unit : SameBlockUnitRows G) :
    ConcreteClosedOrbitFamily :=
  (sourceRowsOfDisplacementClosureSeparation
    closure separated_sq same_block_edges_sq_unit)
      |>.toConcreteClosedOrbitFamily

def squaredMinimalFieldsWithOrbitClosureOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    SquaredMinimalFieldsWithOrbitClosure :=
  (sourceRowsOfGeneratedClosureMetricRowPackage P).toSquaredMinimalFieldsWithOrbitClosure

def concreteClosedOrbitFamilyOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    ConcreteClosedOrbitFamily :=
  (sourceRowsOfGeneratedClosureMetricRowPackage P).toConcreteClosedOrbitFamily

theorem nonempty_sourceRows_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (h : Nonempty (CompletionRows G)) :
    Nonempty SquaredOrbitClosureSourceRows := by
  cases h with
  | intro R =>
      exact Nonempty.intro (sourceRowsOfCompletionRows G R)

theorem nonempty_squaredMinimalFieldsWithOrbitClosure_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (h : Nonempty (CompletionRows G)) :
    Nonempty SquaredMinimalFieldsWithOrbitClosure := by
  exact
    SquaredOrbitClosureSourceW28.nonempty_squaredMinimalFieldsWithOrbitClosure_of_sourceRows
      (nonempty_sourceRows_of_completionRows h)

theorem nonempty_concreteClosedOrbitFamily_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (h : Nonempty (CompletionRows G)) :
    Nonempty ConcreteClosedOrbitFamily := by
  exact
    SquaredOrbitClosureSourceW28.nonempty_concreteClosedOrbitFamily_of_sourceRows
      (nonempty_sourceRows_of_completionRows h)

theorem nonempty_minimalFreePlacementFields_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (h : Nonempty (CompletionRows G)) :
    Nonempty MinimalFreePlacementFields := by
  exact
    SquaredOrbitClosureSourceW28.nonempty_minimalFreePlacementFields_of_sourceRows
      (nonempty_sourceRows_of_completionRows h)

theorem nonempty_sourceRows_of_displacementClosureSeparation
    {G : GeneratedOrbitSkeleton}
    (closure : DisplacementClosureRows G)
    (separated_sq : SeparationRows G)
    (same_block_edges_sq_unit : SameBlockUnitRows G) :
    Nonempty SquaredOrbitClosureSourceRows :=
  Nonempty.intro
    (sourceRowsOfDisplacementClosureSeparation
      closure separated_sq same_block_edges_sq_unit)

theorem nonempty_squaredMinimalFieldsWithOrbitClosure_of_displacementClosureSeparation
    {G : GeneratedOrbitSkeleton}
    (closure : DisplacementClosureRows G)
    (separated_sq : SeparationRows G)
    (same_block_edges_sq_unit : SameBlockUnitRows G) :
    Nonempty SquaredMinimalFieldsWithOrbitClosure :=
  Nonempty.intro
    (squaredMinimalFieldsWithOrbitClosureOfDisplacementClosureSeparation
      closure separated_sq same_block_edges_sq_unit)

theorem nonempty_concreteClosedOrbitFamily_of_displacementClosureSeparation
    {G : GeneratedOrbitSkeleton}
    (closure : DisplacementClosureRows G)
    (separated_sq : SeparationRows G)
    (same_block_edges_sq_unit : SameBlockUnitRows G) :
    Nonempty ConcreteClosedOrbitFamily :=
  Nonempty.intro
    (concreteClosedOrbitFamilyOfDisplacementClosureSeparation
      closure separated_sq same_block_edges_sq_unit)

theorem nonempty_sourceRows_of_generatedClosureMetricRowPackage :
    Nonempty GeneratedClosureMetricRowPackage ->
      Nonempty SquaredOrbitClosureSourceRows := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (sourceRowsOfGeneratedClosureMetricRowPackage P)

theorem nonempty_squaredMinimalFieldsWithOrbitClosure_of_generatedClosureMetricRowPackage :
    Nonempty GeneratedClosureMetricRowPackage ->
      Nonempty SquaredMinimalFieldsWithOrbitClosure := by
  intro h
  exact
    SquaredOrbitClosureSourceW28.nonempty_squaredMinimalFieldsWithOrbitClosure_of_sourceRows
      (nonempty_sourceRows_of_generatedClosureMetricRowPackage h)

theorem nonempty_concreteClosedOrbitFamily_of_generatedClosureMetricRowPackage :
    Nonempty GeneratedClosureMetricRowPackage ->
      Nonempty ConcreteClosedOrbitFamily := by
  intro h
  exact
    SquaredOrbitClosureSourceW28.nonempty_concreteClosedOrbitFamily_of_sourceRows
      (nonempty_sourceRows_of_generatedClosureMetricRowPackage h)

theorem nonempty_minimalFreePlacementFields_of_generatedClosureMetricRowPackage :
    Nonempty GeneratedClosureMetricRowPackage ->
      Nonempty MinimalFreePlacementFields := by
  intro h
  exact
    SquaredOrbitClosureSourceW28.nonempty_minimalFreePlacementFields_of_sourceRows
      (nonempty_sourceRows_of_generatedClosureMetricRowPackage h)

end

end SquaredOrbitClosureCompletionRowsW29
end PachToth

namespace Verified

open PachToth.SquaredOrbitClosureCompletionRowsW29

abbrev PachTothW29CompletionRows
    (G : GeneratedOrbitSkeleton) :
    Prop :=
  CompletionRows G

theorem pachtoth_w29_squaredMinimalFieldsWithOrbitClosure_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (h : Nonempty (PachTothW29CompletionRows G)) :
    Nonempty
      PachToth.ClosedPlacementConcreteConstructionW27.SquaredMinimalFieldsWithOrbitClosure :=
  nonempty_squaredMinimalFieldsWithOrbitClosure_of_completionRows h

theorem pachtoth_w29_concreteClosedOrbitFamily_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (h : Nonempty (PachTothW29CompletionRows G)) :
    Nonempty
      PachToth.ClosedPlacementConcreteConstructionW27.ConcreteClosedOrbitFamily :=
  nonempty_concreteClosedOrbitFamily_of_completionRows h

theorem pachtoth_w29_concreteClosedOrbitFamily_of_displacementClosureSeparation
    {G : GeneratedOrbitSkeleton}
    (closure : DisplacementClosureRows G)
    (separated_sq : SeparationRows G)
    (same_block_edges_sq_unit : SameBlockUnitRows G) :
    Nonempty
      PachToth.ClosedPlacementConcreteConstructionW27.ConcreteClosedOrbitFamily :=
  nonempty_concreteClosedOrbitFamily_of_displacementClosureSeparation
    closure separated_sq same_block_edges_sq_unit

theorem pachtoth_w29_concreteClosedOrbitFamily_of_generatedClosureMetricRowPackage :
    Nonempty GeneratedClosureMetricRowPackage ->
      Nonempty
        PachToth.ClosedPlacementConcreteConstructionW27.ConcreteClosedOrbitFamily :=
  nonempty_concreteClosedOrbitFamily_of_generatedClosureMetricRowPackage

end Verified
end ErdosProblems1066
