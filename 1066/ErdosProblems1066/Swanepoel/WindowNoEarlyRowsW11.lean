import ErdosProblems1066.Swanepoel.WindowContainmentW10
import ErdosProblems1066.Swanepoel.M8WindowContainmentConcrete
import ErdosProblems1066.Swanepoel.Lemma9NoStartConcrete
import ErdosProblems1066.Swanepoel.NoStartInstantiation
import ErdosProblems1066.Swanepoel.NoEarlyTripleConcrete
import ErdosProblems1066.Swanepoel.NoEarlyK23AssemblyW10

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 window/no-early rows

This module packages the W10 window-containment facade together with explicit
no-start and concrete no-early data.  The rows are intentionally conditional:
they assemble supplied fields for each minimal cleared failure into the already
checked W9, no-start-instantiation, and W10 no-early assembly routes.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace WindowNoEarlyRowsW11

open Lemma9NoStartConcrete
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalFailureToTargetConcrete
open MinimalGraphFacts
open NoEarlyK23AssemblyW10
open NoEarlyTripleConcrete
open NoStartInstantiation
open SwanepoelRemainingObligationsW9
open WindowContainmentW10

universe u

noncomputable section

variable {n : Nat}

/-! ## Window rows -/

/-- A W11 window row for the exact labels and turn bounds selected by a W9
base row. -/
structure WindowRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : BaseRow.{u} C hmin
  windowFields : M8LocalWindowContainmentFields base.localLabels base.turnBounds

namespace WindowRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Build the W11 window row from the W10 angle-containment facade. -/
def ofAngleContainmentRow
    {base : BaseRow.{u} C hmin}
    (A : W9BaseAngleContainmentRow.{u} C hmin base) :
    WindowRow.{u} C hmin where
  base := base
  windowFields := A.windowFields

/-- The construction window-containment record carried by the row. -/
def windowContainment
    (W : WindowRow.{u} C hmin) :
    M8WindowContainment W.base.localLabels W.base.turnBounds :=
  W.windowFields.toM8WindowContainment

/-- The same row in the W9 remaining-obligation format. -/
def toW9WindowRow
    (W : WindowRow.{u} C hmin) :
    SwanepoelRemainingObligationsW9.WindowRow.{u} C hmin W.base where
  containment := W.windowContainment

/-- The underlying concrete local window fields. -/
def toLocalWindowContainmentFields
    (W : WindowRow.{u} C hmin) :
    M8LocalWindowContainmentFields W.base.localLabels W.base.turnBounds :=
  W.windowFields

@[simp]
theorem toW9WindowRow_containment
    (W : WindowRow.{u} C hmin) :
    W.toW9WindowRow.containment = W.windowContainment :=
  rfl

@[simp]
theorem ofAngleContainmentRow_windowContainment
    {base : BaseRow.{u} C hmin}
    (A : W9BaseAngleContainmentRow.{u} C hmin base) :
    (ofAngleContainmentRow A).windowContainment = A.windowContainment :=
  rfl

end WindowRow

/-! ## No-early rows -/

/-- A W11 row with window containment and concrete no-early exclusions. -/
structure NoEarlyRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  window : WindowRow.{u} C hmin
  noEarly :
    M8ConcreteNoEarlyTripleEquality
      window.base.localLabels.predicates.data

namespace NoEarlyRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Concrete no-early data viewed as Lemma 9 explicit no-start fields. -/
def noStartFields
    (R : NoEarlyRow.{u} C hmin) :
    M8ConstructionExplicitNoStartFields R.window.base.localLabels :=
  constructionExplicitNoStartFields_of_concreteNoEarly
    (localLabels := R.window.base.localLabels) R.noEarly

/-- The W9 direct no-start row induced by the concrete no-early row. -/
def toW9NoStartRow
    (R : NoEarlyRow.{u} C hmin) :
    NoStartRow.{u} C hmin R.window.base where
  no_start1 := R.noStartFields.no_start1
  no_start2 := R.noStartFields.no_start2
  no_start3 := R.noStartFields.no_start3
  no_start4 := R.noStartFields.no_start4
  no_start5 := R.noStartFields.no_start5

/-- The W9 direct minimal-failure row assembled from window and no-early data. -/
def toW9DirectRow
    (R : NoEarlyRow.{u} C hmin) :
    MinimalFailureDirectRow.{u} C hmin where
  base := R.window.base
  window := R.window.toW9WindowRow
  noStart := R.toW9NoStartRow

/-- The no-start-instantiation target row assembled from the W11 row. -/
def toNoEarlyTargetRow
    (R : NoEarlyRow.{u} C hmin) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRow C hmin where
  labels := R.window.base.labels
  arc := R.window.base.arc
  windowContainment := by
    simpa [BaseRow.localLabels, BaseRow.turnBounds] using
      R.window.windowContainment
  noEarly := by
    simpa [BaseRow.localLabels] using R.noEarly

/-- The W10 no-early assembly row assembled from the W11 row. -/
def toNoEarlyObstructionRow
    (R : NoEarlyRow.{u} C hmin) :
    NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRow C hmin where
  labels := R.window.base.labels
  arc := R.window.base.arc
  noEarly := by
    simpa [BaseRow.localLabels] using R.noEarly
  windowContainment := by
    simpa [BaseRow.localLabels, BaseRow.turnBounds] using
      R.window.windowContainment

/-- The exact concrete minimal-failure row reached from the W11 row. -/
def toMinimalFailureConcreteRow
    (R : NoEarlyRow.{u} C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toW9DirectRow.toMinimalFailureConcreteRow

/-- A fixed minimal cleared failure with a W11 no-early row closes. -/
theorem contradiction
    (R : NoEarlyRow.{u} C hmin) :
    False :=
  R.toW9DirectRow.contradiction

@[simp]
theorem toW9DirectRow_concreteRow
    (R : NoEarlyRow.{u} C hmin) :
    R.toW9DirectRow.toMinimalFailureConcreteRow =
      R.toMinimalFailureConcreteRow :=
  rfl

@[simp]
theorem toNoEarlyTargetRow_concreteNoEarly
    (R : NoEarlyRow.{u} C hmin) :
    (R.toNoEarlyTargetRow.toMinimalFailureConcreteRow).concreteNoEarlyTripleEquality =
      R.noEarly := by
  simp

end NoEarlyRow

/-! ## No-start rows -/

/-- A W11 row with window containment and explicit Lemma 9 no-start fields. -/
structure NoStartRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  window : WindowRow.{u} C hmin
  noStart : M8ConstructionExplicitNoStartFields window.base.localLabels

namespace NoStartRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The explicit no-start row repackaged as concrete no-early exclusions. -/
def noEarly
    (R : NoStartRow.{u} C hmin) :
    M8ConcreteNoEarlyTripleEquality
      R.window.base.localLabels.predicates.data :=
  R.noStart.toConcreteNoEarlyTripleEquality

/-- Forget explicit no-start packaging to the W11 no-early row. -/
def toNoEarlyRow
    (R : NoStartRow.{u} C hmin) :
    NoEarlyRow.{u} C hmin where
  window := R.window
  noEarly := R.noEarly

/-- The W9 direct no-start row induced by the explicit no-start fields. -/
def toW9NoStartRow
    (R : NoStartRow.{u} C hmin) :
    SwanepoelRemainingObligationsW9.NoStartRow.{u} C hmin R.window.base where
  no_start1 := R.noStart.no_start1
  no_start2 := R.noStart.no_start2
  no_start3 := R.noStart.no_start3
  no_start4 := R.noStart.no_start4
  no_start5 := R.noStart.no_start5

/-- The W9 direct minimal-failure row assembled from window and no-start data. -/
def toW9DirectRow
    (R : NoStartRow.{u} C hmin) :
    MinimalFailureDirectRow.{u} C hmin where
  base := R.window.base
  window := R.window.toW9WindowRow
  noStart := R.toW9NoStartRow

/-- The no-start-instantiation target row assembled from the W11 row. -/
def toNoStartTargetRow
    (R : NoStartRow.{u} C hmin) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRow C hmin where
  labels := R.window.base.labels
  arc := R.window.base.arc
  windowContainment := by
    simpa [BaseRow.localLabels, BaseRow.turnBounds] using
      R.window.windowContainment
  noStart := by
    simpa [BaseRow.localLabels] using R.noStart

/-- The W10 no-start assembly row assembled from the W11 row. -/
def toNoStartObstructionRow
    (R : NoStartRow.{u} C hmin) :
    NoEarlyK23AssemblyW10.MinimalFailureNoStartObstructionRow C hmin where
  labels := R.window.base.labels
  arc := R.window.base.arc
  noStart := by
    simpa [BaseRow.localLabels] using R.noStart
  windowContainment := by
    simpa [BaseRow.localLabels, BaseRow.turnBounds] using
      R.window.windowContainment

/-- The exact concrete minimal-failure row reached from the W11 row. -/
def toMinimalFailureConcreteRow
    (R : NoStartRow.{u} C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toW9DirectRow.toMinimalFailureConcreteRow

/-- A fixed minimal cleared failure with a W11 no-start row closes. -/
theorem contradiction
    (R : NoStartRow.{u} C hmin) :
    False :=
  R.toW9DirectRow.contradiction

@[simp]
theorem toNoEarlyRow_toW9DirectRow
    (R : NoStartRow.{u} C hmin) :
    R.toNoEarlyRow.toW9DirectRow = R.toW9DirectRow :=
  rfl

end NoStartRow

/-! ## Uniform matrices -/

/-- Uniform W11 no-early rows for every minimal cleared failure. -/
structure NoEarlyMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        NoEarlyRow.{u} C hmin

namespace NoEarlyMatrix

/-- Route W11 no-early rows to the W9 direct matrix. -/
def toW9DirectMatrix
    (M : NoEarlyMatrix.{u}) :
    DirectMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toW9DirectRow

/-- Route W11 no-early rows to the no-start-instantiation target family. -/
def toNoEarlyTargetRowFamily
    (M : NoEarlyMatrix.{u}) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily where
  row := fun C hmin => (M.row C hmin).toNoEarlyTargetRow

/-- Route W11 no-early rows to the W10 no-early assembly family. -/
def toNoEarlyObstructionRowFamily
    (M : NoEarlyMatrix.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRowFamily where
  row := fun C hmin => (M.row C hmin).toNoEarlyObstructionRow

/-- Convert W11 no-early rows to the concrete rows consumed by the target
route. -/
def toConcreteRows
    (M : NoEarlyMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  fun C hmin => (M.row C hmin).toMinimalFailureConcreteRow

/-- W11 no-early rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : NoEarlyMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toW9DirectMatrix.no_minimalClearedFailure

/-- Public target projection from uniform W11 no-early rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : NoEarlyMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toW9DirectMatrix.targetLowerBoundEightThirtyOne

end NoEarlyMatrix

/-- Uniform W11 no-start rows for every minimal cleared failure. -/
structure NoStartMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        NoStartRow.{u} C hmin

namespace NoStartMatrix

/-- Forget explicit no-start packaging to uniform W11 no-early rows. -/
def toNoEarlyMatrix
    (M : NoStartMatrix.{u}) :
    NoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toNoEarlyRow

/-- Route W11 no-start rows to the W9 direct matrix. -/
def toW9DirectMatrix
    (M : NoStartMatrix.{u}) :
    DirectMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toW9DirectRow

/-- Route W11 no-start rows to the no-start-instantiation target family. -/
def toNoStartTargetRowFamily
    (M : NoStartMatrix.{u}) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRowFamily where
  row := fun C hmin => (M.row C hmin).toNoStartTargetRow

/-- Route W11 no-start rows to the W10 no-start assembly family. -/
def toNoStartObstructionRowFamily
    (M : NoStartMatrix.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureNoStartObstructionRowFamily where
  row := fun C hmin => (M.row C hmin).toNoStartObstructionRow

/-- Route W11 no-start rows to the W10 no-early assembly family. -/
def toNoEarlyObstructionRowFamily
    (M : NoStartMatrix.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRowFamily :=
  M.toNoEarlyMatrix.toNoEarlyObstructionRowFamily

/-- Convert W11 no-start rows to the concrete rows consumed by the target
route. -/
def toConcreteRows
    (M : NoStartMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  fun C hmin => (M.row C hmin).toMinimalFailureConcreteRow

/-- W11 no-start rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : NoStartMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toW9DirectMatrix.no_minimalClearedFailure

/-- Public target projection from uniform W11 no-start rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : NoStartMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toW9DirectMatrix.targetLowerBoundEightThirtyOne

end NoStartMatrix

/-! ## Top-level projection forms -/

theorem no_minimalClearedFailure_of_noEarlyMatrix
    (M : NoEarlyMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.no_minimalClearedFailure

theorem no_minimalClearedFailure_of_noStartMatrix
    (M : NoStartMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne_of_noEarlyMatrix
    (M : NoEarlyMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_noStartMatrix
    (M : NoStartMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

end

end WindowNoEarlyRowsW11
end Swanepoel
end ErdosProblems1066
