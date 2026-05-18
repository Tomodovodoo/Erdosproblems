import ErdosProblems1066.Swanepoel.WindowNoEarlyClosureW11
import ErdosProblems1066.Swanepoel.WindowNoEarlyRowsW11
import ErdosProblems1066.Swanepoel.BoundaryLabelRowsW11
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryMatrixW11
import ErdosProblems1066.Swanepoel.SwanepoelTargetClosureW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 no-early/no-start integrated matrix

This module connects the explicit W11 boundary-label prefix rows to the
checked W11 window/no-early, geometry, and target-closure routes.

The rows deliberately keep the still-missing geometric inputs visible:
window containment is an explicit field, and the no-start variant carries the
five Lemma 9 no-start exclusions as an explicit field.  The matrix below is a
conditional ledger of adapters; it does not add a root import or assert an
unconditional Swanepoel lower bound.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyIntegratedW11

open BoundaryLabelRowsW11
open Lemma9NoStartConcrete
open M8WindowContainmentConcrete
open MinimalGraphFacts
open NoEarlyTripleConcrete

universe u

noncomputable section

variable {n : Nat}

abbrev BasePrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryLabelRowsW11.BoundaryLabelRowPackage.BasePrefix.{u} C hmin

abbrev WindowRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  WindowNoEarlyRowsW11.WindowRow.{u} C hmin

abbrev NoEarlyRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin

abbrev NoStartRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  WindowNoEarlyRowsW11.NoStartRow.{u} C hmin

abbrev W11NoEarlyMatrix :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.{u}

abbrev W11NoStartMatrix :=
  WindowNoEarlyRowsW11.NoStartMatrix.{u}

abbrev W10DirectComponentMatrix :=
  MinimalFailureDirectMatrixW10.DirectComponentMatrix.{u}

abbrev W10MinimalFailureDirectMatrix :=
  SwanepoelW10ClosureMatrix.MinimalFailureDirectW10Matrix.{u}

abbrev GeometryClosureMatrix :=
  MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u}

abbrev NarrowClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.NarrowClosureInputFamily.{u}

abbrev CheckedClosureInputFamily :=
  MinimalFailureGeometryMatrixW11.CheckedClosureInputFamily.{u}

abbrev TargetFacadeMatrix :=
  SwanepoelTargetFacadeW10.Matrix

abbrev MinimalFailureExclusion :=
  SwanepoelTargetClosureW11.MinimalFailureExclusion

abbrev PipelineCleared :=
  SwanepoelTargetClosureW11.PipelineCleared

abbrev W10ProjectionRow (alpha : Type u) :=
  SwanepoelTargetClosureW11.W10ProjectionRow alpha

/-! ## Prefix rows with explicit missing fields -/

/-- A boundary-label prefix plus explicit window containment and concrete
five-start no-early data for the same labels and turn bounds. -/
structure PrefixNoEarlyRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  basePrefix : BasePrefix C hmin
  windowFields :
    M8LocalWindowContainmentFields
      basePrefix.toW10BaseRow.localLabels basePrefix.toW10BaseRow.turnBounds
  noEarly :
    M8ConcreteNoEarlyTripleEquality
      basePrefix.toW10BaseRow.localLabels.predicates.data

namespace PrefixNoEarlyRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The W11 window row obtained from the prefix and explicit containment. -/
def toWindowRow
    (R : PrefixNoEarlyRow C hmin) :
    WindowRow.{u} C hmin where
  base := R.basePrefix.toW10BaseRow
  windowFields := R.windowFields

/-- The W11 concrete no-early row obtained from the explicit source fields. -/
def toNoEarlyRow
    (R : PrefixNoEarlyRow C hmin) :
    NoEarlyRow.{u} C hmin where
  window := R.toWindowRow
  noEarly := R.noEarly

/-- Route the integrated row to the W10 direct-component surface. -/
def toW10DirectComponentRow
    (R : PrefixNoEarlyRow C hmin) :
    MinimalFailureDirectMatrixW10.DirectComponentRow.{u} C hmin :=
  WindowNoEarlyClosureW11.w10DirectComponentRow_of_noEarlyRow
    R.toNoEarlyRow

/-- Route the integrated row to the narrow W11 geometry closure input. -/
def toNarrowClosureInput
    (R : PrefixNoEarlyRow C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toW10DirectComponentRow.toConcreteDataObligations

/-- A fixed integrated no-early row closes through the checked W11 route. -/
theorem contradiction
    (R : PrefixNoEarlyRow C hmin) :
    False :=
  WindowNoEarlyClosureW11.contradiction_of_noEarlyRow R.toNoEarlyRow

@[simp]
theorem toWindowRow_base
    (R : PrefixNoEarlyRow C hmin) :
    R.toWindowRow.base = R.basePrefix.toW10BaseRow :=
  rfl

@[simp]
theorem toWindowRow_windowFields
    (R : PrefixNoEarlyRow C hmin) :
    R.toWindowRow.windowFields = R.windowFields :=
  rfl

@[simp]
theorem toNoEarlyRow_noEarly
    (R : PrefixNoEarlyRow C hmin) :
    R.toNoEarlyRow.noEarly = R.noEarly :=
  rfl

end PrefixNoEarlyRow

/-- A boundary-label prefix plus explicit window containment and the five
Lemma 9 no-start exclusions for the same labels and turn bounds. -/
structure PrefixNoStartRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  basePrefix : BasePrefix C hmin
  windowFields :
    M8LocalWindowContainmentFields
      basePrefix.toW10BaseRow.localLabels basePrefix.toW10BaseRow.turnBounds
  noStart :
    M8ConstructionExplicitNoStartFields basePrefix.toW10BaseRow.localLabels

namespace PrefixNoStartRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The W11 window row obtained from the prefix and explicit containment. -/
def toWindowRow
    (R : PrefixNoStartRow C hmin) :
    WindowRow.{u} C hmin where
  base := R.basePrefix.toW10BaseRow
  windowFields := R.windowFields

/-- The W11 explicit no-start row obtained from the explicit source fields. -/
def toNoStartRow
    (R : PrefixNoStartRow C hmin) :
    NoStartRow.{u} C hmin where
  window := R.toWindowRow
  noStart := R.noStart

/-- Forget explicit no-start packaging to the concrete W11 no-early row. -/
def toNoEarlyRow
    (R : PrefixNoStartRow C hmin) :
    NoEarlyRow.{u} C hmin :=
  R.toNoStartRow.toNoEarlyRow

/-- Route the integrated row to the W10 direct-component surface. -/
def toW10DirectComponentRow
    (R : PrefixNoStartRow C hmin) :
    MinimalFailureDirectMatrixW10.DirectComponentRow.{u} C hmin :=
  WindowNoEarlyClosureW11.w10DirectComponentRow_of_noStartRow
    R.toNoStartRow

/-- Route the integrated row to the narrow W11 geometry closure input. -/
def toNarrowClosureInput
    (R : PrefixNoStartRow C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toW10DirectComponentRow.toConcreteDataObligations

/-- A fixed integrated no-start row closes through the checked W11 route. -/
theorem contradiction
    (R : PrefixNoStartRow C hmin) :
    False :=
  WindowNoEarlyClosureW11.contradiction_of_noStartRow R.toNoStartRow

@[simp]
theorem toWindowRow_base
    (R : PrefixNoStartRow C hmin) :
    R.toWindowRow.base = R.basePrefix.toW10BaseRow :=
  rfl

@[simp]
theorem toWindowRow_windowFields
    (R : PrefixNoStartRow C hmin) :
    R.toWindowRow.windowFields = R.windowFields :=
  rfl

@[simp]
theorem toNoStartRow_noStart
    (R : PrefixNoStartRow C hmin) :
    R.toNoStartRow.noStart = R.noStart :=
  rfl

end PrefixNoStartRow

/-! ## Uniform integrated matrices -/

/-- Uniform integrated no-early rows for every minimal cleared failure. -/
structure PrefixNoEarlyMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PrefixNoEarlyRow C hmin

namespace PrefixNoEarlyMatrix

/-- Forget the integrated rows to the W11 no-early matrix. -/
def toW11NoEarlyMatrix
    (M : PrefixNoEarlyMatrix) :
    W11NoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toNoEarlyRow

/-- Route the integrated rows to the W10 direct-component matrix. -/
def toW10DirectComponentMatrix
    (M : PrefixNoEarlyMatrix) :
    W10DirectComponentMatrix.{u} :=
  WindowNoEarlyClosureW11.w10DirectComponentMatrix_of_noEarlyMatrix
    M.toW11NoEarlyMatrix

/-- Route the integrated rows to the target-facade matrix. -/
def toTargetFacadeMatrix
    (M : PrefixNoEarlyMatrix) :
    TargetFacadeMatrix :=
  WindowNoEarlyClosureW11.targetFacadeMatrix_of_noEarlyMatrix
    M.toW11NoEarlyMatrix

/-- Route the integrated rows to the narrow W11 geometry closure inputs. -/
def toNarrowClosureInputFamily
    (M : PrefixNoEarlyMatrix) :
    NarrowClosureInputFamily.{u} :=
  MinimalFailureGeometryMatrixW11.directComponentMatrixToNarrowClosureInputFamily
    M.toW10DirectComponentMatrix

/-- Route the integrated rows to the checked refined W11 geometry inputs. -/
def toCheckedClosureInputFamily
    (M : PrefixNoEarlyMatrix) :
    CheckedClosureInputFamily.{u} :=
  MinimalFailureGeometryMatrixW11.directComponentMatrixToCheckedClosureInputFamily
    M.toW10DirectComponentMatrix

/-- Integrated no-early rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : PrefixNoEarlyMatrix) :
    MinimalFailureExclusion :=
  WindowNoEarlyClosureW11.no_minimalClearedFailure_of_noEarlyMatrix
    M.toW11NoEarlyMatrix

/-- Integrated no-early rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared
    (M : PrefixNoEarlyMatrix) :
    PipelineCleared :=
  WindowNoEarlyClosureW11.pipelineCleared_of_noEarlyMatrix
    M.toW11NoEarlyMatrix

end PrefixNoEarlyMatrix

/-- Uniform integrated no-start rows for every minimal cleared failure. -/
structure PrefixNoStartMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PrefixNoStartRow C hmin

namespace PrefixNoStartMatrix

/-- Forget the integrated rows to the W11 no-start matrix. -/
def toW11NoStartMatrix
    (M : PrefixNoStartMatrix) :
    W11NoStartMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toNoStartRow

/-- Forget explicit no-start rows to a W11 concrete no-early matrix. -/
def toW11NoEarlyMatrix
    (M : PrefixNoStartMatrix) :
    W11NoEarlyMatrix.{u} :=
  M.toW11NoStartMatrix.toNoEarlyMatrix

/-- Route the integrated rows to the W10 direct-component matrix. -/
def toW10DirectComponentMatrix
    (M : PrefixNoStartMatrix) :
    W10DirectComponentMatrix.{u} :=
  WindowNoEarlyClosureW11.w10DirectComponentMatrix_of_noStartMatrix
    M.toW11NoStartMatrix

/-- Route the integrated rows to the target-facade matrix. -/
def toTargetFacadeMatrix
    (M : PrefixNoStartMatrix) :
    TargetFacadeMatrix :=
  WindowNoEarlyClosureW11.targetFacadeMatrix_of_noStartMatrix
    M.toW11NoStartMatrix

/-- Route the integrated rows to the narrow W11 geometry closure inputs. -/
def toNarrowClosureInputFamily
    (M : PrefixNoStartMatrix) :
    NarrowClosureInputFamily.{u} :=
  MinimalFailureGeometryMatrixW11.directComponentMatrixToNarrowClosureInputFamily
    M.toW10DirectComponentMatrix

/-- Route the integrated rows to the checked refined W11 geometry inputs. -/
def toCheckedClosureInputFamily
    (M : PrefixNoStartMatrix) :
    CheckedClosureInputFamily.{u} :=
  MinimalFailureGeometryMatrixW11.directComponentMatrixToCheckedClosureInputFamily
    M.toW10DirectComponentMatrix

/-- Integrated no-start rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : PrefixNoStartMatrix) :
    MinimalFailureExclusion :=
  WindowNoEarlyClosureW11.no_minimalClearedFailure_of_noStartMatrix
    M.toW11NoStartMatrix

/-- Integrated no-start rows supply the cleared-pipeline predicate. -/
theorem pipelineCleared
    (M : PrefixNoStartMatrix) :
    PipelineCleared :=
  WindowNoEarlyClosureW11.pipelineCleared_of_noStartMatrix
    M.toW11NoStartMatrix

end PrefixNoStartMatrix

/-! ## Integrated route ledger -/

/-- A no-early/no-start route ledger connecting prefix rows to W11 geometry
and target-closure facades.  Each field is an adapter or projection route;
the rows themselves remain explicit inputs. -/
structure Matrix where
  targetClosure : SwanepoelTargetClosureW11.Matrix.{u}
  geometryClosure : MinimalFailureGeometryMatrixW11.Matrix.{u}
  noEarlyToW11Rows : PrefixNoEarlyMatrix -> W11NoEarlyMatrix.{u}
  noStartToW11Rows : PrefixNoStartMatrix -> W11NoStartMatrix.{u}
  noEarlyToDirectComponents :
    PrefixNoEarlyMatrix -> W10DirectComponentMatrix.{u}
  noStartToDirectComponents :
    PrefixNoStartMatrix -> W10DirectComponentMatrix.{u}
  noEarlyToNarrowInputs :
    PrefixNoEarlyMatrix -> NarrowClosureInputFamily.{u}
  noStartToNarrowInputs :
    PrefixNoStartMatrix -> NarrowClosureInputFamily.{u}
  noEarlyToCheckedInputs :
    PrefixNoEarlyMatrix -> CheckedClosureInputFamily.{u}
  noStartToCheckedInputs :
    PrefixNoStartMatrix -> CheckedClosureInputFamily.{u}
  noEarlyToTargetFacade :
    PrefixNoEarlyMatrix -> TargetFacadeMatrix
  noStartToTargetFacade :
    PrefixNoStartMatrix -> TargetFacadeMatrix
  targetFacadeNoMinimal : TargetFacadeMatrix -> MinimalFailureExclusion
  targetFacadePipeline : TargetFacadeMatrix -> PipelineCleared
  targetClosureDirectComponentRoute :
    W10ProjectionRow W10MinimalFailureDirectMatrix
  directComponentGeometryRoute :
    MinimalFailureGeometryMatrixW11.ProjectionRow
      W10MinimalFailureDirectMatrix.{u}

/-- The checked integrated W11 no-early/no-start matrix. -/
def matrix : Matrix.{u} where
  targetClosure := SwanepoelTargetClosureW11.matrix
  geometryClosure := MinimalFailureGeometryMatrixW11.matrix
  noEarlyToW11Rows := PrefixNoEarlyMatrix.toW11NoEarlyMatrix
  noStartToW11Rows := PrefixNoStartMatrix.toW11NoStartMatrix
  noEarlyToDirectComponents :=
    PrefixNoEarlyMatrix.toW10DirectComponentMatrix
  noStartToDirectComponents :=
    PrefixNoStartMatrix.toW10DirectComponentMatrix
  noEarlyToNarrowInputs :=
    PrefixNoEarlyMatrix.toNarrowClosureInputFamily
  noStartToNarrowInputs :=
    PrefixNoStartMatrix.toNarrowClosureInputFamily
  noEarlyToCheckedInputs :=
    PrefixNoEarlyMatrix.toCheckedClosureInputFamily
  noStartToCheckedInputs :=
    PrefixNoStartMatrix.toCheckedClosureInputFamily
  noEarlyToTargetFacade :=
    PrefixNoEarlyMatrix.toTargetFacadeMatrix
  noStartToTargetFacade :=
    PrefixNoStartMatrix.toTargetFacadeMatrix
  targetFacadeNoMinimal :=
    SwanepoelTargetFacadeW10.Matrix.no_minimalClearedFailure
  targetFacadePipeline :=
    SwanepoelTargetFacadeW10.Matrix.pipelineCleared
  targetClosureDirectComponentRoute :=
    SwanepoelW10ClosureMatrix.minimalFailureDirectW10MatrixRow
  directComponentGeometryRoute :=
    MinimalFailureGeometryMatrixW11.directComponentMatrixRow

/-! ## Public non-final projections -/

/-- Minimal-failure exclusion from uniform integrated no-early rows. -/
theorem no_minimalClearedFailure_of_prefixNoEarlyMatrix
    (M : PrefixNoEarlyMatrix) :
    MinimalFailureExclusion :=
  M.no_minimalClearedFailure

/-- Minimal-failure exclusion from uniform integrated no-start rows. -/
theorem no_minimalClearedFailure_of_prefixNoStartMatrix
    (M : PrefixNoStartMatrix) :
    MinimalFailureExclusion :=
  M.no_minimalClearedFailure

/-- Pipeline-cleared projection from uniform integrated no-early rows. -/
theorem pipelineCleared_of_prefixNoEarlyMatrix
    (M : PrefixNoEarlyMatrix) :
    PipelineCleared :=
  M.pipelineCleared

/-- Pipeline-cleared projection from uniform integrated no-start rows. -/
theorem pipelineCleared_of_prefixNoStartMatrix
    (M : PrefixNoStartMatrix) :
    PipelineCleared :=
  M.pipelineCleared

end

end NoEarlyIntegratedW11
end Swanepoel
end ErdosProblems1066
