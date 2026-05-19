import ErdosProblems1066.Swanepoel.Figure8ContainmentAngleBudget
import ErdosProblems1066.Swanepoel.WindowNoEarlyRowsW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W12 Figure 8 containment projections

This module isolates the Figure 8 separated-window data needed for E22.

The existing concrete layers already provide:

* selected Figure 8 distance data for a separated failed pair;
* central-angle containment in the separated turn window;
* the Euclidean fact that the selected central angle is at least `pi / 3`.

This file packages those three facts together and exposes pointwise and
uniform projections for the M8/W10/W11 containment rows.  It introduces no new
geometric estimate.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure8ContainmentW12

open AngleBridgeFacts
open AngleContainmentInterface
open AngleGeometry
open Figure8ContainmentAngleBudget
open Figure8ContainmentConcrete
open Figure8EuclideanFactsConcrete
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open M8ConstructionInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts
open WindowContainmentW10
open WindowNoEarlyRowsW11

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Pointwise extracted Figure 8 data -/

/-- The selected Figure 8 separated-window data with both checked angle facts
visible: the Euclidean lower bound on the central angle and its containment in
the separated turn window. -/
structure Figure8SeparatedWindowData
    (turn : Nat -> Real) (i j : Nat) where
  p : Point
  qi : Point
  qj : Point
  s : Point
  r : Point
  distanceData : Figure8DistanceData p qi qj s r
  central_angle_lower : Real.pi / 3 <= angleAt qi p qj
  central_angle_le_separatedTurn :
    angleAt qi p qj <= separatedTurn turn i j

namespace Figure8SeparatedWindowData

variable {turn : Nat -> Real} {i j : Nat}

/-- Build the W12 extracted-data package from the existing contained-data
record. -/
def ofContainedData
    (D : Figure8SeparatedContainedData turn i j) :
    Figure8SeparatedWindowData turn i j where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData
  central_angle_lower :=
    Figure8EuclideanFactsConcrete.central_angle_lower D.distanceData
  central_angle_le_separatedTurn := D.central_angle_le_separatedTurn

/-- Forget the W12 package to the existing contained-data record. -/
def toContainedData
    (D : Figure8SeparatedWindowData turn i j) :
    Figure8SeparatedContainedData turn i j where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData
  central_angle_le_separatedTurn := D.central_angle_le_separatedTurn

/-- Forget the W12 package to the existing pointwise angle-budget record. -/
def toCentralAngleBudget
    (D : Figure8SeparatedWindowData turn i j) :
    Figure8CentralAngleBudget turn i j where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData
  central_angle_le_separatedTurn := D.central_angle_le_separatedTurn

/-- The extracted Figure 8 data forces the local separated-window lower
bound. -/
theorem separatedTurn_lower
    (D : Figure8SeparatedWindowData turn i j) :
    Real.pi / 3 <= separatedTurn turn i j :=
  le_trans D.central_angle_lower D.central_angle_le_separatedTurn

/-- The same lower bound, routed through the existing angle-budget facade. -/
theorem separatedTurn_lower_via_angleBudget
    (D : Figure8SeparatedWindowData turn i j) :
    Real.pi / 3 <= separatedTurn turn i j :=
  D.toCentralAngleBudget.separatedTurn_lower

/-- The W12 package preserves the selected raw extracted data. -/
def toExtractedData
    (D : Figure8SeparatedWindowData turn i j) :
    Figure8SeparatedExtractedData where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData

end Figure8SeparatedWindowData

/-! ## Uniform Figure 8 witnesses -/

/-- Uniform W12 Figure 8 data for every separated failed pair. -/
def Figure8SeparatedWindowDataWitnesses
    (good : Nat -> Prop) (turn : Nat -> Real) : Type :=
  forall {i j : Nat},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
      Figure8SeparatedWindowData turn i j

/-- Uniform W12 data gives the existing contained-witness predicate. -/
def containedWitnesses_of_dataWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedWindowDataWitnesses good turn) :
    Figure8SeparatedContainedWitnesses good turn :=
  fun {i j} hi hsep hj hbad_i hbad_j =>
    (H (i := i) (j := j) hi hsep hj hbad_i hbad_j).toContainedData

/-- Uniform W12 data gives the existing angle-budget package. -/
def angleBudget_of_dataWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedWindowDataWitnesses good turn) :
    Figure8SeparatedAngleBudget good turn where
  budget := by
    intro i j hi hsep hj hbad_i hbad_j
    exact
      (H (i := i) (j := j) hi hsep hj hbad_i hbad_j).toCentralAngleBudget

/-- Uniform W12 data gives the named Figure 8 E22 lower-bound interface. -/
theorem E22_of_dataWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedWindowDataWitnesses good turn) :
    Figure8SeparatedWindowLowerE22 good turn := by
  intro i j hi hsep hj hbad_i hbad_j
  exact
    (H (i := i) (j := j) hi hsep hj hbad_i hbad_j).separatedTurn_lower

/-- The same E22 projection, routed through the angle-budget facade. -/
theorem E22_of_dataWitnesses_via_angleBudget
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedWindowDataWitnesses good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  (angleBudget_of_dataWitnesses H).E22

/-- Convert the existing Figure 8 containment interface to uniform W12 data. -/
def dataWitnesses_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowDataWitnesses good turn :=
  fun {i j} hi hsep hj hbad_i hbad_j =>
    Figure8SeparatedWindowData.ofContainedData
      (H.containedData (i := i) (j := j) hi hsep hj hbad_i hbad_j)

/-- Atomic Figure 8 distance witnesses plus the actual central-angle
containment row give the W12 selected separated-window data. -/
def dataWitnesses_of_distanceWitnessRowsAndCentralAngleContainmentRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (distanceRows : Figure8SeparatedDistanceWitnessRows good)
    (centralAngleRows :
      Figure8SeparatedCentralAngleContainmentRows good turn) :
    Figure8SeparatedWindowDataWitnesses good turn :=
  dataWitnesses_of_containmentInterface
    (Figure8ContainmentConcrete.containmentInterface_of_distanceWitnessRowsAndCentralAngleContainment
      distanceRows centralAngleRows)

/-- Atomic Figure 8 distance witnesses plus the actual central-angle
containment row give the named E22 lower-bound hypothesis. -/
theorem E22_of_distanceWitnessRowsAndCentralAngleContainmentRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (distanceRows : Figure8SeparatedDistanceWitnessRows good)
    (centralAngleRows :
      Figure8SeparatedCentralAngleContainmentRows good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  E22_of_dataWitnesses
    (dataWitnesses_of_distanceWitnessRowsAndCentralAngleContainmentRows
      distanceRows centralAngleRows)

/-- A Figure 8 containment interface gives E22 through the W12 extracted-data
facade. -/
theorem E22_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  E22_of_dataWitnesses (dataWitnesses_of_containmentInterface H)

/-! ## Honest M8 specializations -/

/-- Uniform W12 Figure 8 data specialized to the local `m = 8` predicate
package. -/
def M8Figure8SeparatedWindowDataWitnesses
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Type :=
  Figure8SeparatedWindowDataWitnesses (M8BrokenLatticeGood P) turn

/-- Uniform W12 Figure 8 data specialized to an honest local `m = 8`
package. -/
abbrev HonestFigure8SeparatedWindowDataWitnesses
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) :=
  M8Figure8SeparatedWindowDataWitnesses P.data turn

/-- Honest W12 Figure 8 data gives the honest E22 lower-bound interface. -/
theorem honestFigure8SeparatedWindowLowerE22_of_dataWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowDataWitnesses P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn :=
  E22_of_dataWitnesses H

/-- Local `m = 8` W12 Figure 8 data gives the raw separated-failures
turn-force interface. -/
theorem m8SeparatedFailuresForceTurn_of_dataWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure8SeparatedWindowDataWitnesses P turn) :
    SeparatedFailuresForceTurn (M8BrokenLatticeGood P) turn :=
  separatedFailuresForceTurn_of_E22
    (E22_of_dataWitnesses (good := M8BrokenLatticeGood P) H)

/-! ## Projections from M8 local window-containment fields -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- W12 Figure 8 data selected by the concrete M8 local window fields. -/
def data_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Figure8SeparatedWindowData turnBounds.turn i j :=
  Figure8SeparatedWindowData.ofContainedData
    (H.figure8ContainedData (i := i) (j := j) hi hsep hj hbad_i hbad_j)

/-- Uniform W12 data selected by the concrete M8 local window fields. -/
def dataWitnesses_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowDataWitnesses
      localLabels.predicates turnBounds.turn :=
  fun {i j} hi hsep hj hbad_i hbad_j =>
    data_of_localWindowContainmentFields H (i := i) (j := j)
      hi hsep hj hbad_i hbad_j

/-- The selected Figure 8 distance package from concrete local fields. -/
theorem distanceData_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Figure8DistanceData
      (data_of_localWindowContainmentFields H hi hsep hj
        hbad_i hbad_j).p
      (data_of_localWindowContainmentFields H hi hsep hj
        hbad_i hbad_j).qi
      (data_of_localWindowContainmentFields H hi hsep hj
        hbad_i hbad_j).qj
      (data_of_localWindowContainmentFields H hi hsep hj
        hbad_i hbad_j).s
      (data_of_localWindowContainmentFields H hi hsep hj
        hbad_i hbad_j).r :=
  (data_of_localWindowContainmentFields H hi hsep hj
    hbad_i hbad_j).distanceData

/-- The selected Figure 8 distance package gives the central-angle lower
bound. -/
theorem central_angle_lower_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Real.pi / 3 <=
      angleAt
        (data_of_localWindowContainmentFields H hi hsep hj
          hbad_i hbad_j).qi
        (data_of_localWindowContainmentFields H hi hsep hj
          hbad_i hbad_j).p
        (data_of_localWindowContainmentFields H hi hsep hj
          hbad_i hbad_j).qj :=
  (data_of_localWindowContainmentFields H hi hsep hj
    hbad_i hbad_j).central_angle_lower

/-- The selected Figure 8 central angle is contained in the separated turn
window. -/
theorem central_angle_le_separatedTurn_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    angleAt
        (data_of_localWindowContainmentFields H hi hsep hj
          hbad_i hbad_j).qi
        (data_of_localWindowContainmentFields H hi hsep hj
          hbad_i hbad_j).p
        (data_of_localWindowContainmentFields H hi hsep hj
          hbad_i hbad_j).qj <=
      separatedTurn turnBounds.turn i j :=
  (data_of_localWindowContainmentFields H hi hsep hj
    hbad_i hbad_j).central_angle_le_separatedTurn

/-- Pointwise E22 from the W12 extracted Figure 8 data selected by local
window fields. -/
theorem separatedTurn_lower_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Real.pi / 3 <= separatedTurn turnBounds.turn i j :=
  (data_of_localWindowContainmentFields H hi hsep hj
    hbad_i hbad_j).separatedTurn_lower

/-- Global honest E22 from the W12 extracted data selected by local window
fields. -/
theorem E22_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  E22_of_dataWitnesses
    (dataWitnesses_of_localWindowContainmentFields H)

/-- Raw separated-failures turn-force projection from the W12 data selected by
local window fields. -/
theorem separatedFailuresForceTurn_of_localWindowContainmentFields
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    SeparatedFailuresForceTurn
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  separatedFailuresForceTurn_of_E22
    (E22_of_localWindowContainmentFields H)

/-! ## W10/W11 row projections -/

/-- W12 Figure 8 data selected by a W10 local angle-containment field. -/
def data_of_localAngleContainmentFields
    (H : LocalAngleContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Figure8SeparatedWindowData turnBounds.turn i j :=
  data_of_localWindowContainmentFields H.windowFields
    hi hsep hj hbad_i hbad_j

/-- Global honest E22 from a W10 local angle-containment field through W12
extracted Figure 8 data. -/
theorem E22_of_localAngleContainmentFields
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  E22_of_localWindowContainmentFields H.windowFields

/-- W12 Figure 8 data selected by a W9 base angle-containment row. -/
def data_of_w9BaseAngleContainmentRow
    {hmin : IsMinimalClearedFailure C}
    {base : SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin}
    (H : W9BaseAngleContainmentRow.{u} C hmin base)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood base.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood base.localLabels.predicates.data j)) :
    Figure8SeparatedWindowData base.turnBounds.turn i j :=
  data_of_localWindowContainmentFields H.windowFields
    hi hsep hj hbad_i hbad_j

/-- Global honest E22 from a W9 base angle-containment row through W12
extracted Figure 8 data. -/
theorem E22_of_w9BaseAngleContainmentRow
    {hmin : IsMinimalClearedFailure C}
    {base : SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin}
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    HonestFigure8SeparatedWindowLowerE22
      base.localLabels.predicates base.turnBounds.turn :=
  E22_of_localWindowContainmentFields H.windowFields

/-- W12 Figure 8 data selected by a W11 window row. -/
def data_of_w11WindowRow
    {hmin : IsMinimalClearedFailure C}
    (W : WindowRow.{u} C hmin)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood W.base.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood W.base.localLabels.predicates.data j)) :
    Figure8SeparatedWindowData W.base.turnBounds.turn i j :=
  data_of_localWindowContainmentFields W.windowFields
    hi hsep hj hbad_i hbad_j

/-- The selected Figure 8 central angle from a W11 window row has the checked
Euclidean lower bound. -/
theorem central_angle_lower_of_w11WindowRow
    {hmin : IsMinimalClearedFailure C}
    (W : WindowRow.{u} C hmin)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood W.base.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood W.base.localLabels.predicates.data j)) :
    Real.pi / 3 <=
      angleAt
        (data_of_w11WindowRow W hi hsep hj hbad_i hbad_j).qi
        (data_of_w11WindowRow W hi hsep hj hbad_i hbad_j).p
        (data_of_w11WindowRow W hi hsep hj hbad_i hbad_j).qj :=
  (data_of_w11WindowRow W hi hsep hj hbad_i hbad_j).central_angle_lower

/-- The selected Figure 8 central angle from a W11 window row is contained in
the separated turn window. -/
theorem central_angle_le_separatedTurn_of_w11WindowRow
    {hmin : IsMinimalClearedFailure C}
    (W : WindowRow.{u} C hmin)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood W.base.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood W.base.localLabels.predicates.data j)) :
    angleAt
        (data_of_w11WindowRow W hi hsep hj hbad_i hbad_j).qi
        (data_of_w11WindowRow W hi hsep hj hbad_i hbad_j).p
        (data_of_w11WindowRow W hi hsep hj hbad_i hbad_j).qj <=
      separatedTurn W.base.turnBounds.turn i j :=
  (data_of_w11WindowRow W hi hsep hj hbad_i hbad_j).central_angle_le_separatedTurn

/-- Pointwise E22 from the W12 extracted Figure 8 data selected by a W11
window row. -/
theorem separatedTurn_lower_of_w11WindowRow
    {hmin : IsMinimalClearedFailure C}
    (W : WindowRow.{u} C hmin)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood W.base.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood W.base.localLabels.predicates.data j)) :
    Real.pi / 3 <= separatedTurn W.base.turnBounds.turn i j :=
  (data_of_w11WindowRow W hi hsep hj hbad_i hbad_j).separatedTurn_lower

/-- Global honest E22 from a W11 window row through W12 extracted Figure 8
data. -/
theorem E22_of_w11WindowRow
    {hmin : IsMinimalClearedFailure C}
    (W : WindowRow.{u} C hmin) :
    HonestFigure8SeparatedWindowLowerE22
      W.base.localLabels.predicates W.base.turnBounds.turn :=
  E22_of_localWindowContainmentFields W.windowFields

end Figure8ContainmentW12
end Swanepoel
end ErdosProblems1066

end
