import ErdosProblems1066.Swanepoel.WindowNoEarlyRowsW11
import ErdosProblems1066.Swanepoel.NoEarlyK23AssemblyW10
import ErdosProblems1066.Swanepoel.MinimalFailureDirectMatrixW10
import ErdosProblems1066.Swanepoel.SwanepoelTargetFacadeW10

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 window/no-early closure facade

This module is a checked closure layer for the W11 window/no-start/no-early
row packages.  It keeps the remaining geometry, label, containment, and
no-early inputs visible in the row packages from `WindowNoEarlyRowsW11`, then
projects those packages to:

* W9 direct minimal-failure matrices;
* W10 direct-component matrices;
* W10 no-start/no-early obstruction assembly families;
* the W10 target facade.

No row family is asserted here without an explicit matrix input.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace WindowNoEarlyClosureW11

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  SwanepoelTargetFacadeW10.Target

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelTargetFacadeW10.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelTargetFacadeW10.PipelineCleared

abbrev W11WindowRow
    (C : _root_.UDConfig n) (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  WindowNoEarlyRowsW11.WindowRow.{u} C hmin

abbrev W11NoEarlyRow
    (C : _root_.UDConfig n) (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin

abbrev W11NoStartRow
    (C : _root_.UDConfig n) (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  WindowNoEarlyRowsW11.NoStartRow.{u} C hmin

abbrev W11NoEarlyMatrix :=
  WindowNoEarlyRowsW11.NoEarlyMatrix.{u}

abbrev W11NoStartMatrix :=
  WindowNoEarlyRowsW11.NoStartMatrix.{u}

abbrev W9DirectMatrix :=
  SwanepoelRemainingObligationsW9.DirectMatrix.{u}

abbrev W10DirectComponentRow
    (C : _root_.UDConfig n) (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  MinimalFailureDirectMatrixW10.DirectComponentRow.{u} C hmin

abbrev W10DirectComponentMatrix :=
  MinimalFailureDirectMatrixW10.DirectComponentMatrix.{u}

/-! ## Pointwise adapters to the W10 direct component surface -/

/-- The topology component selected by a W11 window row. -/
def w10TopologyComponent
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (W : W11WindowRow.{u} C hmin) :
    MinimalFailureDirectMatrixW10.TopologyComponentFields C where
  topology := W.base.topology.topology

/-- The partition/angle component selected by a W11 window row. -/
def w10PartitionAngleComponent
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (W : W11WindowRow.{u} C hmin) :
    MinimalFailureDirectMatrixW10.PartitionAngleComponentFields.{u}
      C (w10TopologyComponent W) where
  outerAngleBounds := W.base.topology.outerAngleBounds
  Subpolygon := W.base.topology.Subpolygon
  subpolygonData := W.base.topology.subpolygonData
  longArc := W.base.topology.longArc

/-- The boundary-label component selected by a W11 window row. -/
def w10LabelComponent
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (W : W11WindowRow.{u} C hmin) :
    MinimalFailureDirectMatrixW10.LabelComponentFields.{u}
      C hmin (w10TopologyComponent W) (w10PartitionAngleComponent W) where
  remainingNoCutSlack := W.base.boundaryLabels.remainingNoCutSlack
  spineCertificate := W.base.boundaryLabels.spineCertificate
  lemma8Existence := W.base.boundaryLabels.lemma8Existence

/-- The containment component selected by a W11 window row. -/
def w10ContainmentComponent
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (W : W11WindowRow.{u} C hmin) :
    MinimalFailureDirectMatrixW10.ContainmentComponentFields.{u}
      C hmin (w10TopologyComponent W) (w10PartitionAngleComponent W)
      (w10LabelComponent W) where
  containment := W.windowContainment

/-- The no-early component selected by a W11 no-early row. -/
def w10NoEarlyComponent_of_noEarlyRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : W11NoEarlyRow.{u} C hmin) :
    MinimalFailureDirectMatrixW10.NoEarlyComponentFields.{u}
      C hmin (w10TopologyComponent R.window)
      (w10PartitionAngleComponent R.window)
      (w10LabelComponent R.window) where
  noEarly := R.noEarly

/-- The no-early component selected by a W11 explicit no-start row. -/
def w10NoEarlyComponent_of_noStartRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : W11NoStartRow.{u} C hmin) :
    MinimalFailureDirectMatrixW10.NoEarlyComponentFields.{u}
      C hmin (w10TopologyComponent R.window)
      (w10PartitionAngleComponent R.window)
      (w10LabelComponent R.window) where
  noEarly := R.noEarly

/-- View a W11 no-early row as a W10 direct component row. -/
def w10DirectComponentRow_of_noEarlyRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : W11NoEarlyRow.{u} C hmin) :
    W10DirectComponentRow.{u} C hmin where
  topology := w10TopologyComponent R.window
  partitionAngle := w10PartitionAngleComponent R.window
  labels := w10LabelComponent R.window
  containment := w10ContainmentComponent R.window
  noEarly := w10NoEarlyComponent_of_noEarlyRow R

/-- View a W11 explicit no-start row as a W10 direct component row. -/
def w10DirectComponentRow_of_noStartRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : W11NoStartRow.{u} C hmin) :
    W10DirectComponentRow.{u} C hmin where
  topology := w10TopologyComponent R.window
  partitionAngle := w10PartitionAngleComponent R.window
  labels := w10LabelComponent R.window
  containment := w10ContainmentComponent R.window
  noEarly := w10NoEarlyComponent_of_noStartRow R

/-- A fixed W11 no-early row closes through the W10 direct component route. -/
theorem contradiction_of_noEarlyRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : W11NoEarlyRow.{u} C hmin) :
    False :=
  (w10DirectComponentRow_of_noEarlyRow R).contradiction

/-- A fixed W11 no-start row closes through the W10 direct component route. -/
theorem contradiction_of_noStartRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : W11NoStartRow.{u} C hmin) :
    False :=
  (w10DirectComponentRow_of_noStartRow R).contradiction

/-! ## Uniform matrix adapters -/

/-- Route W11 no-early rows to the W9 direct matrix. -/
def w9DirectMatrix_of_noEarlyMatrix
    (M : W11NoEarlyMatrix.{u}) :
    W9DirectMatrix.{u} :=
  M.toW9DirectMatrix

/-- Route W11 no-start rows to the W9 direct matrix. -/
def w9DirectMatrix_of_noStartMatrix
    (M : W11NoStartMatrix.{u}) :
    W9DirectMatrix.{u} :=
  M.toW9DirectMatrix

/-- Route W11 no-early rows to the W10 direct-component matrix. -/
def w10DirectComponentMatrix_of_noEarlyMatrix
    (M : W11NoEarlyMatrix.{u}) :
    W10DirectComponentMatrix.{u} where
  row := fun C hmin => w10DirectComponentRow_of_noEarlyRow (M.row C hmin)

/-- Route W11 no-start rows to the W10 direct-component matrix. -/
def w10DirectComponentMatrix_of_noStartMatrix
    (M : W11NoStartMatrix.{u}) :
    W10DirectComponentMatrix.{u} where
  row := fun C hmin => w10DirectComponentRow_of_noStartRow (M.row C hmin)

/-- Route W11 no-early rows to the W10 no-early obstruction family. -/
def noEarlyObstructionRows_of_noEarlyMatrix
    (M : W11NoEarlyMatrix.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRowFamily :=
  M.toNoEarlyObstructionRowFamily

/-- Route W11 no-start rows to the W10 no-start obstruction family. -/
def noStartObstructionRows_of_noStartMatrix
    (M : W11NoStartMatrix.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureNoStartObstructionRowFamily :=
  M.toNoStartObstructionRowFamily

/-- Route W11 no-start rows to the W10 no-early obstruction family. -/
def noEarlyObstructionRows_of_noStartMatrix
    (M : W11NoStartMatrix.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRowFamily :=
  M.toNoEarlyObstructionRowFamily

/-- View W11 no-early rows as W10 target-facade data. -/
def targetFacadeMatrix_of_noEarlyMatrix
    (M : W11NoEarlyMatrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix where
  excludesMinimalFailures :=
    (w10DirectComponentMatrix_of_noEarlyMatrix M).no_minimalClearedFailure

/-- View W11 no-start rows as W10 target-facade data. -/
def targetFacadeMatrix_of_noStartMatrix
    (M : W11NoStartMatrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix where
  excludesMinimalFailures :=
    (w10DirectComponentMatrix_of_noStartMatrix M).no_minimalClearedFailure

/-! ## Target-facing conditional projections -/

/-- W11 no-early rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure_of_noEarlyMatrix
    (M : W11NoEarlyMatrix.{u}) :
    MinimalFailureExclusion :=
  (targetFacadeMatrix_of_noEarlyMatrix M).no_minimalClearedFailure

/-- W11 no-start rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure_of_noStartMatrix
    (M : W11NoStartMatrix.{u}) :
    MinimalFailureExclusion :=
  (targetFacadeMatrix_of_noStartMatrix M).no_minimalClearedFailure

/-- W11 no-early rows supply the cleared pipeline predicate. -/
theorem pipelineCleared_of_noEarlyMatrix
    (M : W11NoEarlyMatrix.{u}) :
    PipelineCleared :=
  (targetFacadeMatrix_of_noEarlyMatrix M).pipelineCleared

/-- W11 no-start rows supply the cleared pipeline predicate. -/
theorem pipelineCleared_of_noStartMatrix
    (M : W11NoStartMatrix.{u}) :
    PipelineCleared :=
  (targetFacadeMatrix_of_noStartMatrix M).pipelineCleared

/-- Conditional Swanepoel target from uniform W11 no-early rows. -/
theorem targetLowerBoundEightThirtyOne_of_noEarlyMatrix
    (M : W11NoEarlyMatrix.{u}) :
    Target :=
  (targetFacadeMatrix_of_noEarlyMatrix M).targetLowerBoundEightThirtyOne

/-- Conditional Swanepoel target from uniform W11 no-start rows. -/
theorem targetLowerBoundEightThirtyOne_of_noStartMatrix
    (M : W11NoStartMatrix.{u}) :
    Target :=
  (targetFacadeMatrix_of_noStartMatrix M).targetLowerBoundEightThirtyOne

end

end WindowNoEarlyClosureW11
end Swanepoel
end ErdosProblems1066
