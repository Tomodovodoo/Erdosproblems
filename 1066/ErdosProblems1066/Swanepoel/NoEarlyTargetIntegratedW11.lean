import ErdosProblems1066.Swanepoel.NoEarlyIntegratedW11
import ErdosProblems1066.Swanepoel.WindowNoEarlyClosureW11
import ErdosProblems1066.Swanepoel.BoundaryLabelClosureW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11
import ErdosProblems1066.Swanepoel.SwanepoelW11IntegratedMatrix

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 target-facing no-early integration

This module keeps the no-early inputs visible all the way to the Swanepoel
target facades.  The row records display the boundary-label prefix, the local
window fields, and the supplied no-early or no-start fields.  The matrix
records are uniform input families; the target projections below remain
conditional on one of those families.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyTargetIntegratedW11

open BoundaryLabelClosureW11
open BoundaryLabelRowsW11
open Lemma9NoStartConcrete
open M8WindowContainmentConcrete
open MinimalGraphFacts
open NoEarlyTripleConcrete

universe u v

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetClosureMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetClosureMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetClosureMatrixW11.PipelineCleared

abbrev LabelPrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryLabelClosureW11.LabelBasePrefix.{u} C hmin

abbrev WindowFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : LabelPrefix.{u} C hmin) :=
  M8LocalWindowContainmentFields
    B.toW10BaseRow.localLabels B.toW10BaseRow.turnBounds

abbrev NoEarlyFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : LabelPrefix.{u} C hmin) :=
  M8ConcreteNoEarlyTripleEquality
    B.toW10BaseRow.localLabels.predicates.data

abbrev NoStartFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : LabelPrefix.{u} C hmin) :=
  M8ConstructionExplicitNoStartFields B.toW10BaseRow.localLabels

abbrev W11NoEarlyMatrix :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.{u}

abbrev W11NoStartMatrix :=
  WindowNoEarlyRowsW11.NoStartMatrix.{u}

abbrev W10TargetFacadeMatrix :=
  SwanepoelTargetFacadeW10.Matrix

abbrev NarrowClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u}

abbrev CheckedClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u}

abbrev W10DirectComponentMatrix :=
  MinimalFailureDirectMatrixW10.DirectComponentMatrix.{u}

/-! ## Explicit target-facing rows -/

/-- Boundary labels, window containment, and concrete no-early fields for one
minimal cleared failure. -/
structure ExplicitNoEarlyRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labelPrefix : LabelPrefix.{u} C hmin
  windowFields : WindowFields labelPrefix
  noEarly : NoEarlyFields labelPrefix

namespace ExplicitNoEarlyRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget the target-facing spelling to the integrated W11 no-early row. -/
def toPrefixNoEarlyRow
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    NoEarlyIntegratedW11.PrefixNoEarlyRow.{u} C hmin where
  basePrefix := R.labelPrefix
  windowFields := R.windowFields
  noEarly := R.noEarly

/-- The W11 window row selected by the explicit fields. -/
def toWindowRow
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    WindowNoEarlyRowsW11.WindowRow.{u} C hmin :=
  R.toPrefixNoEarlyRow.toWindowRow

/-- The W11 no-early row selected by the explicit fields. -/
def toNoEarlyRow
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toPrefixNoEarlyRow.toNoEarlyRow

/-- The target-facing concrete no-early row selected by the same fields. -/
def toNoEarlyTargetRow
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRow C hmin :=
  R.toNoEarlyRow.toNoEarlyTargetRow

/-- The W10 direct component row reached from the same explicit fields. -/
def toW10DirectComponentRow
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    MinimalFailureDirectMatrixW10.DirectComponentRow.{u} C hmin :=
  R.toPrefixNoEarlyRow.toW10DirectComponentRow

/-- The narrow W11 closure input reached from the same explicit fields. -/
def toNarrowClosureInput
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toPrefixNoEarlyRow.toNarrowClosureInput

/-- A fixed row closes through the checked W11 no-early route. -/
theorem contradiction
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    False :=
  R.toPrefixNoEarlyRow.contradiction

@[simp]
theorem toPrefixNoEarlyRow_labelPrefix
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    R.toPrefixNoEarlyRow.basePrefix = R.labelPrefix :=
  rfl

@[simp]
theorem toPrefixNoEarlyRow_windowFields
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    R.toPrefixNoEarlyRow.windowFields = R.windowFields :=
  rfl

@[simp]
theorem toPrefixNoEarlyRow_noEarly
    (R : ExplicitNoEarlyRow.{u} C hmin) :
    R.toPrefixNoEarlyRow.noEarly = R.noEarly :=
  rfl

end ExplicitNoEarlyRow

/-- Boundary labels, window containment, and the five explicit no-start fields
for one minimal cleared failure. -/
structure ExplicitNoStartRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labelPrefix : LabelPrefix.{u} C hmin
  windowFields : WindowFields labelPrefix
  noStart : NoStartFields labelPrefix

namespace ExplicitNoStartRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget the target-facing spelling to the integrated W11 no-start row. -/
def toPrefixNoStartRow
    (R : ExplicitNoStartRow.{u} C hmin) :
    NoEarlyIntegratedW11.PrefixNoStartRow.{u} C hmin where
  basePrefix := R.labelPrefix
  windowFields := R.windowFields
  noStart := R.noStart

/-- The W11 window row selected by the explicit fields. -/
def toWindowRow
    (R : ExplicitNoStartRow.{u} C hmin) :
    WindowNoEarlyRowsW11.WindowRow.{u} C hmin :=
  R.toPrefixNoStartRow.toWindowRow

/-- The W11 no-start row selected by the explicit fields. -/
def toNoStartRow
    (R : ExplicitNoStartRow.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin :=
  R.toPrefixNoStartRow.toNoStartRow

/-- The W11 no-early row obtained from the explicit no-start fields. -/
def toNoEarlyRow
    (R : ExplicitNoStartRow.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toPrefixNoStartRow.toNoEarlyRow

/-- The target-facing explicit no-start row selected by the same fields. -/
def toNoStartTargetRow
    (R : ExplicitNoStartRow.{u} C hmin) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRow C hmin :=
  R.toNoStartRow.toNoStartTargetRow

/-- The target-facing no-early row obtained from the explicit no-start fields.
-/
def toNoEarlyTargetRow
    (R : ExplicitNoStartRow.{u} C hmin) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRow C hmin :=
  R.toNoEarlyRow.toNoEarlyTargetRow

/-- The W10 direct component row reached from the same explicit fields. -/
def toW10DirectComponentRow
    (R : ExplicitNoStartRow.{u} C hmin) :
    MinimalFailureDirectMatrixW10.DirectComponentRow.{u} C hmin :=
  R.toPrefixNoStartRow.toW10DirectComponentRow

/-- The narrow W11 closure input reached from the same explicit fields. -/
def toNarrowClosureInput
    (R : ExplicitNoStartRow.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toPrefixNoStartRow.toNarrowClosureInput

/-- A fixed row closes through the checked W11 no-start route. -/
theorem contradiction
    (R : ExplicitNoStartRow.{u} C hmin) :
    False :=
  R.toPrefixNoStartRow.contradiction

@[simp]
theorem toPrefixNoStartRow_labelPrefix
    (R : ExplicitNoStartRow.{u} C hmin) :
    R.toPrefixNoStartRow.basePrefix = R.labelPrefix :=
  rfl

@[simp]
theorem toPrefixNoStartRow_windowFields
    (R : ExplicitNoStartRow.{u} C hmin) :
    R.toPrefixNoStartRow.windowFields = R.windowFields :=
  rfl

@[simp]
theorem toPrefixNoStartRow_noStart
    (R : ExplicitNoStartRow.{u} C hmin) :
    R.toPrefixNoStartRow.noStart = R.noStart :=
  rfl

end ExplicitNoStartRow

/-- Boundary labels, window containment, explicit no-start fields, and a
concrete no-early package over the same local labels. -/
structure ExplicitNoStartNoEarlyRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labelPrefix : LabelPrefix.{u} C hmin
  windowFields : WindowFields labelPrefix
  noStart : NoStartFields labelPrefix
  noEarly : NoEarlyFields labelPrefix

namespace ExplicitNoStartNoEarlyRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget to the explicit no-early row. -/
def toExplicitNoEarlyRow
    (R : ExplicitNoStartNoEarlyRow.{u} C hmin) :
    ExplicitNoEarlyRow.{u} C hmin where
  labelPrefix := R.labelPrefix
  windowFields := R.windowFields
  noEarly := R.noEarly

/-- Forget to the explicit no-start row. -/
def toExplicitNoStartRow
    (R : ExplicitNoStartNoEarlyRow.{u} C hmin) :
    ExplicitNoStartRow.{u} C hmin where
  labelPrefix := R.labelPrefix
  windowFields := R.windowFields
  noStart := R.noStart

/-- The W11 no-early row selected by the concrete no-early field. -/
def toNoEarlyRow
    (R : ExplicitNoStartNoEarlyRow.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toExplicitNoEarlyRow.toNoEarlyRow

/-- The W11 no-start row selected by the explicit no-start field. -/
def toNoStartRow
    (R : ExplicitNoStartNoEarlyRow.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin :=
  R.toExplicitNoStartRow.toNoStartRow

/-- The target-facing no-early row selected by the concrete no-early field. -/
def toNoEarlyTargetRow
    (R : ExplicitNoStartNoEarlyRow.{u} C hmin) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRow C hmin :=
  R.toExplicitNoEarlyRow.toNoEarlyTargetRow

/-- The target-facing no-start row selected by the explicit no-start field. -/
def toNoStartTargetRow
    (R : ExplicitNoStartNoEarlyRow.{u} C hmin) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRow C hmin :=
  R.toExplicitNoStartRow.toNoStartTargetRow

/-- The no-early field alone closes the fixed row. -/
theorem contradiction_of_noEarly
    (R : ExplicitNoStartNoEarlyRow.{u} C hmin) :
    False :=
  R.toExplicitNoEarlyRow.contradiction

/-- The no-start field alone closes the fixed row. -/
theorem contradiction_of_noStart
    (R : ExplicitNoStartNoEarlyRow.{u} C hmin) :
    False :=
  R.toExplicitNoStartRow.contradiction

end ExplicitNoStartNoEarlyRow

/-! ## Boundary-label closure adapters -/

namespace ExplicitNoEarlyRow

/-- Extract the target-facing no-early row from a checked boundary-label
closure row. -/
def ofBoundaryLabelClosureRow
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : BoundaryLabelClosureW11.Row.{u} C hmin) :
    ExplicitNoEarlyRow.{u} C hmin where
  labelPrefix := R.labelPrefix
  windowFields := R.containment.localContainment
  noEarly := R.noEarly.concreteNoEarly

end ExplicitNoEarlyRow

/-! ## Uniform explicit matrices -/

/-- Uniform explicit no-early rows for every minimal cleared failure. -/
structure ExplicitNoEarlyMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        ExplicitNoEarlyRow.{u} C hmin

namespace ExplicitNoEarlyMatrix

/-- Forget to the integrated no-early matrix. -/
def toPrefixNoEarlyMatrix
    (M : ExplicitNoEarlyMatrix.{u}) :
    NoEarlyIntegratedW11.PrefixNoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toPrefixNoEarlyRow

/-- Forget to the checked W11 no-early rows. -/
def toW11NoEarlyMatrix
    (M : ExplicitNoEarlyMatrix.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toPrefixNoEarlyMatrix.toW11NoEarlyMatrix

/-- Route to the W10 direct component matrix. -/
def toW10DirectComponentMatrix
    (M : ExplicitNoEarlyMatrix.{u}) :
    W10DirectComponentMatrix.{u} :=
  M.toPrefixNoEarlyMatrix.toW10DirectComponentMatrix

/-- Route to the W10 target facade. -/
def toW10TargetFacadeMatrix
    (M : ExplicitNoEarlyMatrix.{u}) :
    W10TargetFacadeMatrix :=
  M.toPrefixNoEarlyMatrix.toTargetFacadeMatrix

/-- Route to the target-facing no-early row family. -/
def toNoEarlyTargetRowFamily
    (M : ExplicitNoEarlyMatrix.{u}) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily where
  row := fun C hmin => (M.row C hmin).toNoEarlyTargetRow

/-- Route to the narrow W11 closure inputs. -/
def toNarrowClosureInputFamily
    (M : ExplicitNoEarlyMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toPrefixNoEarlyMatrix.toNarrowClosureInputFamily

/-- Route to the refined checked W11 closure inputs. -/
def toCheckedClosureInputFamily
    (M : ExplicitNoEarlyMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toPrefixNoEarlyMatrix.toCheckedClosureInputFamily

/-- Uniform explicit no-early rows rule out minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : ExplicitNoEarlyMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toPrefixNoEarlyMatrix.no_minimalClearedFailure

/-- Uniform explicit no-early rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared
    (M : ExplicitNoEarlyMatrix.{u}) :
    PipelineCleared :=
  M.toPrefixNoEarlyMatrix.pipelineCleared

/-- Conditional target projection from uniform explicit no-early rows. -/
theorem targetClosure
    (M : ExplicitNoEarlyMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.targetLowerBoundEightThirtyOne_of_noEarlyMatrix
    M.toW11NoEarlyMatrix

end ExplicitNoEarlyMatrix

/-- Uniform explicit no-start rows for every minimal cleared failure. -/
structure ExplicitNoStartMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        ExplicitNoStartRow.{u} C hmin

namespace ExplicitNoStartMatrix

/-- Forget to the integrated no-start matrix. -/
def toPrefixNoStartMatrix
    (M : ExplicitNoStartMatrix.{u}) :
    NoEarlyIntegratedW11.PrefixNoStartMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toPrefixNoStartRow

/-- Forget to the checked W11 no-start rows. -/
def toW11NoStartMatrix
    (M : ExplicitNoStartMatrix.{u}) :
    W11NoStartMatrix.{u} :=
  M.toPrefixNoStartMatrix.toW11NoStartMatrix

/-- Forget explicit no-start rows to checked W11 no-early rows. -/
def toW11NoEarlyMatrix
    (M : ExplicitNoStartMatrix.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toPrefixNoStartMatrix.toW11NoEarlyMatrix

/-- Route to the W10 direct component matrix. -/
def toW10DirectComponentMatrix
    (M : ExplicitNoStartMatrix.{u}) :
    W10DirectComponentMatrix.{u} :=
  M.toPrefixNoStartMatrix.toW10DirectComponentMatrix

/-- Route to the W10 target facade. -/
def toW10TargetFacadeMatrix
    (M : ExplicitNoStartMatrix.{u}) :
    W10TargetFacadeMatrix :=
  M.toPrefixNoStartMatrix.toTargetFacadeMatrix

/-- Route to the target-facing explicit no-start row family. -/
def toNoStartTargetRowFamily
    (M : ExplicitNoStartMatrix.{u}) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRowFamily where
  row := fun C hmin => (M.row C hmin).toNoStartTargetRow

/-- Route to the target-facing no-early row family induced by no-start. -/
def toNoEarlyTargetRowFamily
    (M : ExplicitNoStartMatrix.{u}) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily where
  row := fun C hmin => (M.row C hmin).toNoEarlyTargetRow

/-- Route to the narrow W11 closure inputs. -/
def toNarrowClosureInputFamily
    (M : ExplicitNoStartMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toPrefixNoStartMatrix.toNarrowClosureInputFamily

/-- Route to the refined checked W11 closure inputs. -/
def toCheckedClosureInputFamily
    (M : ExplicitNoStartMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toPrefixNoStartMatrix.toCheckedClosureInputFamily

/-- Uniform explicit no-start rows rule out minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : ExplicitNoStartMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toPrefixNoStartMatrix.no_minimalClearedFailure

/-- Uniform explicit no-start rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared
    (M : ExplicitNoStartMatrix.{u}) :
    PipelineCleared :=
  M.toPrefixNoStartMatrix.pipelineCleared

/-- Conditional target projection from uniform explicit no-start rows. -/
theorem targetClosure
    (M : ExplicitNoStartMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.targetLowerBoundEightThirtyOne_of_noStartMatrix
    M.toW11NoStartMatrix

end ExplicitNoStartMatrix

/-- Uniform explicit no-start and no-early rows for every minimal cleared
failure. -/
structure ExplicitNoStartNoEarlyMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        ExplicitNoStartNoEarlyRow.{u} C hmin

namespace ExplicitNoStartNoEarlyMatrix

/-- Forget to the uniform explicit no-early matrix. -/
def toExplicitNoEarlyMatrix
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    ExplicitNoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toExplicitNoEarlyRow

/-- Forget to the uniform explicit no-start matrix. -/
def toExplicitNoStartMatrix
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    ExplicitNoStartMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toExplicitNoStartRow

/-- The checked W11 no-early matrix selected by the no-early fields. -/
def toW11NoEarlyMatrix
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    W11NoEarlyMatrix.{u} :=
  M.toExplicitNoEarlyMatrix.toW11NoEarlyMatrix

/-- The checked W11 no-start matrix selected by the no-start fields. -/
def toW11NoStartMatrix
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    W11NoStartMatrix.{u} :=
  M.toExplicitNoStartMatrix.toW11NoStartMatrix

/-- The W10 target facade reached through the no-early fields. -/
def toW10TargetFacadeMatrix
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    W10TargetFacadeMatrix :=
  M.toExplicitNoEarlyMatrix.toW10TargetFacadeMatrix

/-- Uniform no-start and no-early rows rule out minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toExplicitNoEarlyMatrix.no_minimalClearedFailure

/-- Uniform no-start and no-early rows supply the cleared-pipeline predicate.
-/
theorem pipelineCleared
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    PipelineCleared :=
  M.toExplicitNoEarlyMatrix.pipelineCleared

/-- Conditional target projection from uniform no-start and no-early rows. -/
theorem targetClosure
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    Target :=
  M.toExplicitNoEarlyMatrix.targetClosure

end ExplicitNoStartNoEarlyMatrix

/-! ## Boundary-label matrix bridge -/

/-- Convert checked boundary-label closure rows to explicit no-early rows. -/
def explicitNoEarlyMatrixOfBoundaryLabelClosure
    (M : BoundaryLabelClosureW11.Matrix.{u}) :
    ExplicitNoEarlyMatrix.{u} where
  row := fun C hmin =>
    ExplicitNoEarlyRow.ofBoundaryLabelClosureRow (M.row C hmin)

/-- Conditional target projection through the explicit no-early bridge from
boundary-label closure rows. -/
theorem targetClosure_of_boundaryLabelClosureMatrix
    (M : BoundaryLabelClosureW11.Matrix.{u}) :
    Target :=
  (explicitNoEarlyMatrixOfBoundaryLabelClosure M).targetClosure

/-! ## Target route ledgers -/

/-- A target route that keeps the W10 target-facade projection visible. -/
structure TargetFacadeRoute (alpha : Sort v) : Sort (max 1 v) where
  facade : alpha -> W10TargetFacadeMatrix
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace TargetFacadeRoute

/-- Build a route from a W10 target-facade projection. -/
def ofFacade
    {alpha : Sort v}
    (facade : alpha -> W10TargetFacadeMatrix) :
    TargetFacadeRoute alpha where
  facade := facade
  noMinimal := fun x => (facade x).no_minimalClearedFailure
  pipeline := fun x => (facade x).pipelineCleared
  target := fun x => (facade x).targetLowerBoundEightThirtyOne

end TargetFacadeRoute

/-- W10 facade route from uniform explicit no-early rows. -/
def explicitNoEarlyFacadeRoute :
    TargetFacadeRoute (ExplicitNoEarlyMatrix.{u}) :=
  TargetFacadeRoute.ofFacade ExplicitNoEarlyMatrix.toW10TargetFacadeMatrix

/-- W10 facade route from uniform explicit no-start rows. -/
def explicitNoStartFacadeRoute :
    TargetFacadeRoute (ExplicitNoStartMatrix.{u}) :=
  TargetFacadeRoute.ofFacade ExplicitNoStartMatrix.toW10TargetFacadeMatrix

/-- W10 facade route from uniform rows carrying both no-start and no-early
fields. -/
def explicitNoStartNoEarlyFacadeRoute :
    TargetFacadeRoute (ExplicitNoStartNoEarlyMatrix.{u}) :=
  TargetFacadeRoute.ofFacade
    ExplicitNoStartNoEarlyMatrix.toW10TargetFacadeMatrix

/-- W11 target-closure route from uniform explicit no-early rows. -/
def explicitNoEarlyTargetClosureRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (ExplicitNoEarlyMatrix.{u}) where
  noMinimal := ExplicitNoEarlyMatrix.no_minimalClearedFailure
  pipeline := ExplicitNoEarlyMatrix.pipelineCleared
  target := ExplicitNoEarlyMatrix.targetClosure

/-- W11 target-closure route from uniform explicit no-start rows. -/
def explicitNoStartTargetClosureRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (ExplicitNoStartMatrix.{u}) where
  noMinimal := ExplicitNoStartMatrix.no_minimalClearedFailure
  pipeline := ExplicitNoStartMatrix.pipelineCleared
  target := ExplicitNoStartMatrix.targetClosure

/-- W11 target-closure route from uniform rows carrying both no-start and
no-early fields. -/
def explicitNoStartNoEarlyTargetClosureRoute :
    TargetClosureMatrixW11.TargetProjectionRow
      (ExplicitNoStartNoEarlyMatrix.{u}) where
  noMinimal := ExplicitNoStartNoEarlyMatrix.no_minimalClearedFailure
  pipeline := ExplicitNoStartNoEarlyMatrix.pipelineCleared
  target := ExplicitNoStartNoEarlyMatrix.targetClosure

/-- Swanepoel integrated route from uniform explicit no-early rows. -/
def explicitNoEarlySwanepoelIntegratedRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (ExplicitNoEarlyMatrix.{u}) where
  noMinimal := ExplicitNoEarlyMatrix.no_minimalClearedFailure
  pipeline := ExplicitNoEarlyMatrix.pipelineCleared
  target := ExplicitNoEarlyMatrix.targetClosure

/-- Swanepoel integrated route from uniform explicit no-start rows. -/
def explicitNoStartSwanepoelIntegratedRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (ExplicitNoStartMatrix.{u}) where
  noMinimal := ExplicitNoStartMatrix.no_minimalClearedFailure
  pipeline := ExplicitNoStartMatrix.pipelineCleared
  target := ExplicitNoStartMatrix.targetClosure

/-- Swanepoel integrated route from uniform rows carrying both no-start and
no-early fields. -/
def explicitNoStartNoEarlySwanepoelIntegratedRoute :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (ExplicitNoStartNoEarlyMatrix.{u}) where
  noMinimal := ExplicitNoStartNoEarlyMatrix.no_minimalClearedFailure
  pipeline := ExplicitNoStartNoEarlyMatrix.pipelineCleared
  target := ExplicitNoStartNoEarlyMatrix.targetClosure

/-- The target-facing no-early ledgers added by this module.  Each entry is a
conditional route from an explicit uniform input family. -/
structure Matrix : Type (u + 1) where
  noEarlyIntegrated : NoEarlyIntegratedW11.Matrix.{u}
  targetClosure : TargetClosureMatrixW11.Matrix.{u}
  swanepoelIntegrated : SwanepoelW11IntegratedMatrix.Matrix.{u}
  noEarlyFacade : TargetFacadeRoute (ExplicitNoEarlyMatrix.{u})
  noStartFacade : TargetFacadeRoute (ExplicitNoStartMatrix.{u})
  noStartNoEarlyFacade :
    TargetFacadeRoute (ExplicitNoStartNoEarlyMatrix.{u})
  noEarlyTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (ExplicitNoEarlyMatrix.{u})
  noStartTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (ExplicitNoStartMatrix.{u})
  noStartNoEarlyTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (ExplicitNoStartNoEarlyMatrix.{u})
  noEarlySwanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (ExplicitNoEarlyMatrix.{u})
  noStartSwanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (ExplicitNoStartMatrix.{u})
  noStartNoEarlySwanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (ExplicitNoStartNoEarlyMatrix.{u})

/-- The checked target-facing no-early integration matrix. -/
def matrix : Matrix.{u} where
  noEarlyIntegrated := NoEarlyIntegratedW11.matrix
  targetClosure := TargetClosureMatrixW11.matrix
  swanepoelIntegrated := SwanepoelW11IntegratedMatrix.matrix
  noEarlyFacade := explicitNoEarlyFacadeRoute
  noStartFacade := explicitNoStartFacadeRoute
  noStartNoEarlyFacade := explicitNoStartNoEarlyFacadeRoute
  noEarlyTargetClosure := explicitNoEarlyTargetClosureRoute
  noStartTargetClosure := explicitNoStartTargetClosureRoute
  noStartNoEarlyTargetClosure := explicitNoStartNoEarlyTargetClosureRoute
  noEarlySwanepoelIntegrated := explicitNoEarlySwanepoelIntegratedRoute
  noStartSwanepoelIntegrated := explicitNoStartSwanepoelIntegratedRoute
  noStartNoEarlySwanepoelIntegrated :=
    explicitNoStartNoEarlySwanepoelIntegratedRoute

/-! ## Public conditional projections -/

/-- Minimal-failure exclusion from uniform explicit no-early rows. -/
theorem no_minimalClearedFailure_of_explicitNoEarlyMatrix
    (M : ExplicitNoEarlyMatrix.{u}) :
    MinimalFailureExclusion :=
  M.no_minimalClearedFailure

/-- Pipeline-cleared projection from uniform explicit no-early rows. -/
theorem pipelineCleared_of_explicitNoEarlyMatrix
    (M : ExplicitNoEarlyMatrix.{u}) :
    PipelineCleared :=
  M.pipelineCleared

/-- Conditional target projection from uniform explicit no-early rows. -/
theorem targetClosure_of_explicitNoEarlyMatrix
    (M : ExplicitNoEarlyMatrix.{u}) :
    Target :=
  M.targetClosure

/-- Minimal-failure exclusion from uniform explicit no-start rows. -/
theorem no_minimalClearedFailure_of_explicitNoStartMatrix
    (M : ExplicitNoStartMatrix.{u}) :
    MinimalFailureExclusion :=
  M.no_minimalClearedFailure

/-- Pipeline-cleared projection from uniform explicit no-start rows. -/
theorem pipelineCleared_of_explicitNoStartMatrix
    (M : ExplicitNoStartMatrix.{u}) :
    PipelineCleared :=
  M.pipelineCleared

/-- Conditional target projection from uniform explicit no-start rows. -/
theorem targetClosure_of_explicitNoStartMatrix
    (M : ExplicitNoStartMatrix.{u}) :
    Target :=
  M.targetClosure

/-- Minimal-failure exclusion from uniform explicit no-start and no-early
rows. -/
theorem no_minimalClearedFailure_of_explicitNoStartNoEarlyMatrix
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    MinimalFailureExclusion :=
  M.no_minimalClearedFailure

/-- Pipeline-cleared projection from uniform explicit no-start and no-early
rows. -/
theorem pipelineCleared_of_explicitNoStartNoEarlyMatrix
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    PipelineCleared :=
  M.pipelineCleared

/-- Conditional target projection from uniform explicit no-start and no-early
rows. -/
theorem targetClosure_of_explicitNoStartNoEarlyMatrix
    (M : ExplicitNoStartNoEarlyMatrix.{u}) :
    Target :=
  M.targetClosure

end

end NoEarlyTargetIntegratedW11
end Swanepoel
end ErdosProblems1066
