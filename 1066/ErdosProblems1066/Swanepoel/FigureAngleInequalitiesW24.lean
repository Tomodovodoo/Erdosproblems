import ErdosProblems1066.Swanepoel.FigureAngleContainmentConcreteW23

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W24 selected Figure angle inequalities

The concrete Euclidean Figure 8/Figure 9 files already prove the metric half
of the Figure 8/9 route: the selected Figure 8 central angle and Figure 9
left angle are at least `pi / 3`.  The remaining data is not a Euclidean
consequence by itself, because it mentions the external turn function: the
selected angle must be contained in the corresponding turn window.

This module isolates that selected-witness surface and routes it downstream to
the named E22/E23 hypotheses.  It also connects the stronger W23 universal
exact angle-containment package to the same selected Euclidean witness route.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureAngleInequalitiesW24

open AngleBridgeFacts
open AngleContainmentBridgeProducerW19
open AngleContainmentInterface
open AngleGeometry
open FigureAngleContainmentConcreteW23
open FigureExactAngleCertificateInhabitationW22
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open M8ConstructionInterface
open MinimalGraphFacts

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Minimal selected Euclidean witness fields -/

/-- The selected Figure 8/Figure 9 Euclidean witness surface needed to reach
E22/E23.

Each selected witness carries distance data, the Euclidean lower angle bound
derived from that distance data, and the remaining exact turn-window
containment for the selected angle.  This is intentionally weaker than the W23
universal containment fields, which quantify over every distance package at
the same indices. -/
structure SelectedFigureEuclideanWitnessFields
    (good : Nat -> Prop) (turn : Nat -> Real) : Type where
  figure8 :
    Figure8EuclideanFactsConcrete.Figure8SeparatedEuclideanFactWitnesses
      good turn
  figure9_left :
    Figure9EuclideanFactsConcrete.Figure9AdjacentLeftEuclideanFactWitnesses
      good turn

namespace SelectedFigureEuclideanWitnessFields

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- Select the Figure 8 Euclidean witness at one separated failed pair. -/
def figure8Data
    (H : SelectedFigureEuclideanWitnessFields good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Figure8EuclideanFactsConcrete.Figure8SeparatedEuclideanFacts turn i j :=
  H.figure8 hi hsep hj hbad_i hbad_j

/-- Select the Figure 9 Euclidean witness at one adjacent failed pair. -/
def figure9LeftData
    (H : SelectedFigureEuclideanWitnessFields good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Figure9EuclideanFactsConcrete.Figure9AdjacentLeftEuclideanFacts turn i :=
  H.figure9_left hi hi_next hbad_i hbad_next

/-- The selected Figure 8 exact containment inequality. -/
theorem figure8_selected_angle_le_separatedTurn
    (H : SelectedFigureEuclideanWitnessFields good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    angleAt
        (H.figure8Data hi hsep hj hbad_i hbad_j).qi
        (H.figure8Data hi hsep hj hbad_i hbad_j).p
        (H.figure8Data hi hsep hj hbad_i hbad_j).qj <=
      separatedTurn turn i j :=
  (H.figure8Data hi hsep hj hbad_i hbad_j).central_angle_le_separatedTurn

/-- The selected Figure 8 Euclidean angle lower bound. -/
theorem figure8_selected_angle_lower
    (H : SelectedFigureEuclideanWitnessFields good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Real.pi / 3 <=
      angleAt
        (H.figure8Data hi hsep hj hbad_i hbad_j).qi
        (H.figure8Data hi hsep hj hbad_i hbad_j).p
        (H.figure8Data hi hsep hj hbad_i hbad_j).qj :=
  (H.figure8Data hi hsep hj hbad_i hbad_j).central_angle_lower

/-- The selected Figure 8 witness gives the pointwise E22 lower bound. -/
theorem figure8_selected_separatedTurn_lower
    (H : SelectedFigureEuclideanWitnessFields good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Real.pi / 3 <= separatedTurn turn i j :=
  (H.figure8Data hi hsep hj hbad_i hbad_j).separatedTurn_lower

/-- The selected Figure 9 exact left-angle containment inequality. -/
theorem figure9_selected_left_angle_le_adjacentTurn
    (H : SelectedFigureEuclideanWitnessFields good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    angleAt
        (H.figure9LeftData hi hi_next hbad_i hbad_next).p
        (H.figure9LeftData hi hi_next hbad_i hbad_next).qi
        (H.figure9LeftData hi hi_next hbad_i hbad_next).s <=
      adjacentTurn turn i :=
  (H.figure9LeftData hi hi_next hbad_i hbad_next).left_angle_le_adjacentTurn

/-- The selected Figure 9 Euclidean left-angle lower bound. -/
theorem figure9_selected_left_angle_lower
    (H : SelectedFigureEuclideanWitnessFields good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Real.pi / 3 <=
      angleAt
        (H.figure9LeftData hi hi_next hbad_i hbad_next).p
        (H.figure9LeftData hi hi_next hbad_i hbad_next).qi
        (H.figure9LeftData hi hi_next hbad_i hbad_next).s :=
  (H.figure9LeftData hi hi_next hbad_i hbad_next).left_angle_lower

/-- The selected Figure 9 witness gives the pointwise E23 lower bound. -/
theorem figure9_selected_adjacentTurn_lower
    (H : SelectedFigureEuclideanWitnessFields good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Real.pi / 3 <= adjacentTurn turn i :=
  (H.figure9LeftData hi hi_next hbad_i hbad_next).adjacentTurn_lower

/-- Forget the selected Figure 8 Euclidean fields to W12 Figure 8 witnesses. -/
def figure8W12Witnesses
    (H : SelectedFigureEuclideanWitnessFields good turn) :
    Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn :=
  fun {i j} hi hsep hj hbad_i hbad_j =>
    let D := H.figure8Data (i := i) (j := j) hi hsep hj hbad_i hbad_j
    { p := D.p
      qi := D.qi
      qj := D.qj
      s := D.s
      r := D.r
      distanceData := D.distanceData
      central_angle_lower := D.central_angle_lower
      central_angle_le_separatedTurn := D.central_angle_le_separatedTurn }

/-- Forget the selected Figure 9 Euclidean fields to W12 Figure 9 witnesses. -/
def figure9W12Witnesses
    (H : SelectedFigureEuclideanWitnessFields good turn) :
    Figure9ContainmentW12.AdjacentWindowWitnesses good turn :=
  fun {i} hi hi_next hbad_i hbad_next =>
    let D := H.figure9LeftData (i := i) hi hi_next hbad_i hbad_next
    { p := D.p
      qi := D.qi
      qj := D.qj
      s := D.s
      r := D.r
      distanceData := D.distanceData
      left_angle_le_adjacentTurn := D.left_angle_le_adjacentTurn }

/-- The selected Figure 8 Euclidean witnesses imply E22. -/
theorem E22 (H : SelectedFigureEuclideanWitnessFields good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  Figure8EuclideanFactsConcrete.E22_of_euclideanFactWitnesses_direct
    H.figure8

/-- The selected Figure 9 Euclidean witnesses imply E23. -/
theorem E23 (H : SelectedFigureEuclideanWitnessFields good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  Figure9EuclideanFactsConcrete.E23_of_euclideanFactWitnesses_direct
    H.figure9_left

/-- The selected Euclidean witness fields give the paired E22/E23 lower
bounds through the concrete Figure 8/Figure 9 Euclidean files. -/
theorem E22_E23 (H : SelectedFigureEuclideanWitnessFields good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  And.intro H.E22 H.E23

/-- E22 in the raw separated-failures turn-force shape. -/
theorem separatedFailuresForceTurn
    (H : SelectedFigureEuclideanWitnessFields good turn) :
    SeparatedFailuresForceTurn good turn :=
  separatedFailuresForceTurn_of_E22 H.E22

/-- E23 in the raw adjacent-failures turn-force shape. -/
theorem adjacentFailuresForceTurn
    (H : SelectedFigureEuclideanWitnessFields good turn) :
    AdjacentFailuresForceTurn good turn :=
  adjacentFailuresForceTurn_of_E23 H.E23

end SelectedFigureEuclideanWitnessFields

/-! ## Constructors from W12 and W23 data -/

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- W12 selected Figure 8/Figure 9 witnesses are already enough to build the
minimal selected Euclidean witness fields. -/
def selectedFields_of_w12Witnesses
    (figure8 :
      Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn)
    (figure9 :
      Figure9ContainmentW12.AdjacentWindowWitnesses good turn) :
    SelectedFigureEuclideanWitnessFields good turn where
  figure8 := fun {i j} hi hsep hj hbad_i hbad_j =>
    Figure8EuclideanFactsConcrete.separatedFacts_of_containedData
      ((figure8 (i := i) (j := j) hi hsep hj hbad_i hbad_j).toContainedData)
  figure9_left :=
    Figure9ContainmentW12.euclideanFactWitnesses_of_witnesses figure9

/-- W23 universal exact angle inequalities plus W12 selected distance
witnesses give selected Euclidean witness fields.  The universal W23
inequalities supply only the turn-window containment; the Euclidean lower
bounds are rebuilt from the selected concrete distance packages. -/
def selectedFields_of_exactFigureAngleInequalities
    (H : ExactFigureAngleInequalities good turn)
    (figure8 :
      Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn)
    (figure9 :
      Figure9ContainmentW12.AdjacentWindowWitnesses good turn) :
    SelectedFigureEuclideanWitnessFields good turn where
  figure8 := fun {i j} hi hsep hj hbad_i hbad_j =>
    let D := figure8 (i := i) (j := j) hi hsep hj hbad_i hbad_j
    Figure8EuclideanFactsConcrete.separatedFacts_of_distanceContainment
      D.distanceData
      (ExactFigureAngleInequalities.figure8_apply
        H hi hsep hj hbad_i hbad_j D.distanceData)
  figure9_left := fun {i} hi hi_next hbad_i hbad_next =>
    let D := figure9 (i := i) hi hi_next hbad_i hbad_next
    Figure9EuclideanFactsConcrete.adjacentLeftFacts_of_distanceContainment
      D.distanceData
      (ExactFigureAngleInequalities.figure9_left_apply
        H hi hi_next hbad_i hbad_next D.distanceData)

/-- A combined angle-containment bridge gives selected Euclidean witness
fields through the W23 exact inequality package and the W12 selected
witnesses. -/
def selectedFields_of_angleContainmentBridges
    (A : AngleContainmentBridges good turn) :
    SelectedFigureEuclideanWitnessFields good turn :=
  selectedFields_of_exactFigureAngleInequalities
    (ExactFigureAngleInequalities.ofAngleContainmentBridges A)
    (Figure8ContainmentW12.dataWitnesses_of_containmentInterface A.figure8)
    (Figure9ContainmentW12.witnesses_of_containmentInterface A.figure9)

/-- W12 selected witnesses give E22/E23 through the selected Euclidean witness
route. -/
theorem E22_E23_of_w12Witnesses
    (figure8 :
      Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn)
    (figure9 :
      Figure9ContainmentW12.AdjacentWindowWitnesses good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (selectedFields_of_w12Witnesses figure8 figure9).E22_E23

/-- W23 exact angle inequalities, together with W12 selected witnesses, give
E22/E23 through the concrete Euclidean Figure 8/Figure 9 files. -/
theorem E22_E23_of_exactFigureAngleInequalities
    (H : ExactFigureAngleInequalities good turn)
    (figure8 :
      Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn)
    (figure9 :
      Figure9ContainmentW12.AdjacentWindowWitnesses good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (selectedFields_of_exactFigureAngleInequalities H figure8 figure9).E22_E23

/-- A combined angle-containment bridge gives E22/E23 through W23, W12, and
the concrete Euclidean Figure files. -/
theorem E22_E23_of_angleContainmentBridges
    (A : AngleContainmentBridges good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  (selectedFields_of_angleContainmentBridges A).E22_E23

/-! ## Local M8 specializations -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- Selected Euclidean witness fields for one honest M8 local row. -/
abbrev LocalSelectedFigureEuclideanWitnessFields
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  SelectedFigureEuclideanWitnessFields
    (M8BrokenLatticeGood localLabels.predicates.data)
    turnBounds.turn

/-- W22 local exact data gives the selected Euclidean witness fields exposed
by W23. -/
def localSelectedFields_of_localExactData
    (D : LocalExactAngleData localLabels turnBounds) :
    LocalSelectedFigureEuclideanWitnessFields localLabels turnBounds where
  figure8 :=
    FigureAngleContainmentConcreteW23.figure8EuclideanFactWitnesses_of_localExactData
      D
  figure9_left :=
    FigureAngleContainmentConcreteW23.figure9EuclideanFactWitnesses_of_localExactData
      D

/-- Local W23 exact angle inequalities plus W12 selected witnesses give the
selected Euclidean witness fields. -/
def localSelectedFields_of_w12WitnessesAndInequalities
    (figure8 :
      Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
        localLabels.predicates turnBounds.turn)
    (figure9 :
      Figure9ContainmentW12.HonestAdjacentWindowWitnesses
        localLabels.predicates turnBounds.turn)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    LocalSelectedFigureEuclideanWitnessFields localLabels turnBounds :=
  selectedFields_of_exactFigureAngleInequalities H figure8 figure9

/-- Local exact data gives E22/E23 through the selected Euclidean witness
route. -/
theorem local_E22_E23_of_localExactData
    (D : LocalExactAngleData localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (localSelectedFields_of_localExactData D).E22_E23

/-- Local W23 exact angle inequalities and W12 witnesses give E22/E23 through
the selected Euclidean witness route. -/
theorem local_E22_E23_of_w12WitnessesAndInequalities
    (figure8 :
      Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
        localLabels.predicates turnBounds.turn)
    (figure9 :
      Figure9ContainmentW12.HonestAdjacentWindowWitnesses
        localLabels.predicates turnBounds.turn)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  (localSelectedFields_of_w12WitnessesAndInequalities figure8 figure9 H).E22_E23

end FigureAngleInequalitiesW24
end Swanepoel

namespace Verified

abbrev SwanepoelW24SelectedFigureEuclideanWitnessFields :=
  Swanepoel.FigureAngleInequalitiesW24.SelectedFigureEuclideanWitnessFields

theorem swanepoelW24_E22_E23_of_selectedFigureEuclideanWitnessFields
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : SwanepoelW24SelectedFigureEuclideanWitnessFields good turn) :
    Swanepoel.Lemma10AnalyticBridge.Figure8SeparatedWindowLowerE22
        good turn /\
      Swanepoel.Lemma10AnalyticBridge.Figure9AdjacentWindowLowerE23
        good turn :=
  Swanepoel.FigureAngleInequalitiesW24.SelectedFigureEuclideanWitnessFields.E22_E23
    H

end Verified
end ErdosProblems1066

end
