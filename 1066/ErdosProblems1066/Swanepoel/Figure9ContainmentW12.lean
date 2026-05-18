import ErdosProblems1066.Swanepoel.Figure9ContainmentAngleBudget
import ErdosProblems1066.Swanepoel.WindowContainmentW10

set_option autoImplicit false

/-!
# W12 Figure 9 adjacent-window containment

This module is a narrow extraction layer for the Figure 9 / E23 side of
Swanepoel Lemma 10.  It turns the selected adjacent failed-label witness into
a concrete record carrying:

* the Figure 9 distance data,
* the left-angle containment in the adjacent turn window, and
* the resulting `pi / 3` lower bound for that adjacent window.

No new geometric assumption is introduced here; the record is assembled from
the existing containment witnesses, and the lower bound is routed through the
checked Figure 9 Euclidean/angle-to-turn lemmas.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure9ContainmentW12

open AngleBridgeFacts
open AngleContainmentInterface
open AngleGeometry
open Figure9ContainmentAngleBudget
open Figure9ContainmentConcrete
open Figure9EuclideanFactsConcrete
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open LocalConfigurations
open M8ConstructionInterface
open M8WindowGeometryFromContainment
open MinimalGraphFacts
open WindowContainmentW10

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## One adjacent Figure 9 window -/

/-- Fully extracted data for one adjacent Figure 9 window.

The distance package is the Figure 9 metric content; the final field is the
left-angle containment needed to turn that metric content into E23. -/
structure AdjacentWindowData (turn : Nat -> Real) (i : Nat) where
  p : Point
  qi : Point
  qj : Point
  s : Point
  r : Point
  distanceData : Figure9DistanceData p qi qj s r
  left_angle_le_adjacentTurn :
    angleAt p qi s <= adjacentTurn turn i

namespace AdjacentWindowData

/-- Build the W12 datum from raw Figure 9 distance data and left-angle
containment. -/
def ofDistanceContainment
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    AdjacentWindowData turn i where
  p := p
  qi := qi
  qj := qj
  s := s
  r := r
  distanceData := D
  left_angle_le_adjacentTurn := hcontained

/-- Build the W12 datum from the existing contained-data record. -/
def ofContainedData {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftContainedData turn i) :
    AdjacentWindowData turn i :=
  ofDistanceContainment D.distanceData D.left_angle_le_adjacentTurn

/-- Forget the W12 datum to the existing contained-data record. -/
def toContainedData {turn : Nat -> Real} {i : Nat}
    (D : AdjacentWindowData turn i) :
    Figure9AdjacentLeftContainedData turn i where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData
  left_angle_le_adjacentTurn := D.left_angle_le_adjacentTurn

/-- Forget the W12 datum to the selected Figure 9 Euclidean fact package. -/
def toEuclideanFacts {turn : Nat -> Real} {i : Nat}
    (D : AdjacentWindowData turn i) :
    Figure9AdjacentLeftEuclideanFacts turn i :=
  adjacentLeftFacts_of_distanceContainment
    D.distanceData D.left_angle_le_adjacentTurn

/-- The left comparison angle selected by the W12 datum is at least
`pi / 3`. -/
theorem left_angle_lower {turn : Nat -> Real} {i : Nat}
    (D : AdjacentWindowData turn i) :
    Real.pi / 3 <= angleAt D.p D.qi D.s :=
  leftAngle_lower_of_distanceData D.distanceData

/-- The selected left angle is contained in the adjacent turn window. -/
theorem left_angle_contained {turn : Nat -> Real} {i : Nat}
    (D : AdjacentWindowData turn i) :
    angleAt D.p D.qi D.s <= adjacentTurn turn i :=
  D.left_angle_le_adjacentTurn

/-- The W12 datum gives the local Figure 9 / E23 adjacent-window lower bound.
-/
theorem adjacentTurn_lower {turn : Nat -> Real} {i : Nat}
    (D : AdjacentWindowData turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_distanceData_leftContainment
    D.distanceData D.left_angle_le_adjacentTurn

end AdjacentWindowData

/-! ## Uniform adjacent failed-window witnesses -/

/-- W12 witnesses for every adjacent failed pair in the Lemma 10 window. -/
def AdjacentWindowWitnesses
    (good : Nat -> Prop) (turn : Nat -> Real) : Type :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
      AdjacentWindowData turn i

/-- Convert W12 witnesses to the contained-witness shape used by the existing
Figure 9 containment layer. -/
def containedWitnesses_of_witnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AdjacentWindowWitnesses good turn) :
    Figure9AdjacentLeftContainedWitnesses good turn :=
  fun {i} hi hi_next hbad_i hbad_next =>
    (H (i := i) hi hi_next hbad_i hbad_next).toContainedData

/-- Convert W12 witnesses to the selected Euclidean fact witnesses expected
downstream. -/
def euclideanFactWitnesses_of_witnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AdjacentWindowWitnesses good turn) :
    Figure9AdjacentLeftEuclideanFactWitnesses good turn :=
  fun {i} hi hi_next hbad_i hbad_next =>
    (H (i := i) hi hi_next hbad_i hbad_next).toEuclideanFacts

/-- W12 witnesses give the adjacent-window E23 lower-bound hypothesis. -/
theorem E23_of_witnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : AdjacentWindowWitnesses good turn) :
    Figure9AdjacentWindowLowerE23 good turn := by
  intro i hi hi_next hbad_i hbad_next
  exact (H (i := i) hi hi_next hbad_i hbad_next).adjacentTurn_lower

/-- A Figure 9 adjacent-left containment interface supplies W12 witnesses by
selecting its contained data at each failed adjacent pair. -/
def witnesses_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    AdjacentWindowWitnesses good turn :=
  fun {i} hi hi_next hbad_i hbad_next =>
    AdjacentWindowData.ofContainedData
      (H.containedData (i := i) hi hi_next hbad_i hbad_next)

/-- Pointwise W12 datum selected from a containment interface. -/
def datum_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    AdjacentWindowData turn i :=
  witnesses_of_containmentInterface H hi hi_next hbad_i hbad_next

/-- The selected distance package extracted from a containment interface. -/
theorem distanceData_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Figure9DistanceData
      (datum_of_containmentInterface H hi hi_next hbad_i hbad_next).p
      (datum_of_containmentInterface H hi hi_next hbad_i hbad_next).qi
      (datum_of_containmentInterface H hi hi_next hbad_i hbad_next).qj
      (datum_of_containmentInterface H hi hi_next hbad_i hbad_next).s
      (datum_of_containmentInterface H hi hi_next hbad_i hbad_next).r :=
  (datum_of_containmentInterface H hi hi_next hbad_i hbad_next).distanceData

/-- The selected left-angle containment extracted from a containment
interface. -/
theorem left_angle_contained_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    angleAt
        (datum_of_containmentInterface H hi hi_next hbad_i hbad_next).p
        (datum_of_containmentInterface H hi hi_next hbad_i hbad_next).qi
        (datum_of_containmentInterface H hi hi_next hbad_i hbad_next).s <=
      adjacentTurn turn i :=
  (datum_of_containmentInterface H hi hi_next hbad_i
    hbad_next).left_angle_contained

/-- The selected adjacent-window lower bound extracted from a containment
interface. -/
theorem adjacentTurn_lower_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Real.pi / 3 <= adjacentTurn turn i :=
  (datum_of_containmentInterface H hi hi_next hbad_i
    hbad_next).adjacentTurn_lower

/-- A containment interface gives E23 through the W12 selected data. -/
theorem E23_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_witnesses (witnesses_of_containmentInterface H)

/-! ## Honest failed-label projections -/

/-- Honest W12 witnesses specialized to an `m = 8` local predicate package. -/
abbrev HonestAdjacentWindowWitnesses
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) :=
  AdjacentWindowWitnesses (M8BrokenLatticeGood P.data) turn

/-- A contained Figure 9 window package supplies honest W12 witnesses. -/
def honestWitnesses_of_windowContainment
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn) :
    HonestAdjacentWindowWitnesses P turn :=
  fun {_i} hi hi_next hbad_i hbad_next =>
    AdjacentWindowData.ofContainedData
      (H.data hi hi_next hbad_i hbad_next)

/-- Adjacent failed honest labels select the W12 datum. -/
def honestDatum_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    AdjacentWindowData turn i :=
  AdjacentWindowData.ofContainedData
    (honestContainedData_of_labelFailures H
      hi hi_next hbad_i hbad_next)

/-- Adjacent failed honest labels extract the concrete Figure 9 distance data.
-/
theorem honestDistanceData_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Figure9DistanceData
      (honestDatum_of_labelFailures H hi hi_next
        hbad_i hbad_next).p
      (honestDatum_of_labelFailures H hi hi_next
        hbad_i hbad_next).qi
      (honestDatum_of_labelFailures H hi hi_next
        hbad_i hbad_next).qj
      (honestDatum_of_labelFailures H hi hi_next
        hbad_i hbad_next).s
      (honestDatum_of_labelFailures H hi hi_next
        hbad_i hbad_next).r :=
  (honestDatum_of_labelFailures H hi hi_next
    hbad_i hbad_next).distanceData

/-- Adjacent failed honest labels select a left angle contained in the
adjacent turn window. -/
theorem honest_left_angle_contained_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    angleAt
        (honestDatum_of_labelFailures H hi hi_next
          hbad_i hbad_next).p
        (honestDatum_of_labelFailures H hi hi_next
          hbad_i hbad_next).qi
        (honestDatum_of_labelFailures H hi hi_next
          hbad_i hbad_next).s <=
      adjacentTurn turn i :=
  (honestDatum_of_labelFailures H hi hi_next
    hbad_i hbad_next).left_angle_contained

/-- Adjacent failed honest labels select a Figure 9 left angle bounded below
by `pi / 3`. -/
theorem honest_left_angle_lower_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Real.pi / 3 <=
      angleAt
        (honestDatum_of_labelFailures H hi hi_next
          hbad_i hbad_next).p
        (honestDatum_of_labelFailures H hi hi_next
          hbad_i hbad_next).qi
        (honestDatum_of_labelFailures H hi hi_next
          hbad_i hbad_next).s :=
  (honestDatum_of_labelFailures H hi hi_next
    hbad_i hbad_next).left_angle_lower

/-- Adjacent failed honest labels give the E23 adjacent-window lower bound. -/
theorem honest_adjacentTurn_lower_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Real.pi / 3 <= adjacentTurn turn i :=
  (honestDatum_of_labelFailures H hi hi_next
    hbad_i hbad_next).adjacentTurn_lower

/-- Honest W12 witnesses imply the honest E23 lower-bound hypothesis. -/
theorem honestE23_of_witnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestAdjacentWindowWitnesses P turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  E23_of_witnesses H

/-- Honest W12 witnesses provide the Euclidean fact witnesses requested by
the downstream Figure 9 route. -/
def honestEuclideanFactWitnesses_of_witnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestAdjacentWindowWitnesses P turn) :
    HonestFigure9AdjacentLeftEuclideanFactWitnesses P turn :=
  euclideanFactWitnesses_of_witnesses H

/-! ## Construction-level projections -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- The Figure 9 field of an M8 window-containment package as W12 witnesses. -/
def honestWitnesses_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestAdjacentWindowWitnesses
      localLabels.predicates turnBounds.turn :=
  witnesses_of_containmentInterface W.figure9_left

/-- Adjacent failed honest labels select W12 data from an M8
window-containment package. -/
def honestDatum_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    AdjacentWindowData turnBounds.turn i :=
  AdjacentWindowData.ofContainedData
    (honestContainedData_of_m8WindowContainment_labelFailures
      W hi hi_next hbad_i hbad_next)

/-- Adjacent failed honest labels extract Figure 9 distance data from an M8
window-containment package. -/
theorem honestDistanceData_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    Figure9DistanceData
      (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
        hbad_i hbad_next).p
      (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
        hbad_i hbad_next).qi
      (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
        hbad_i hbad_next).qj
      (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
        hbad_i hbad_next).s
      (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
        hbad_i hbad_next).r :=
  (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
    hbad_i hbad_next).distanceData

/-- Adjacent failed honest labels select the required left-angle containment
from an M8 window-containment package. -/
theorem honest_left_angle_contained_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    angleAt
        (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
          hbad_i hbad_next).p
        (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
          hbad_i hbad_next).qi
        (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
          hbad_i hbad_next).s <=
      adjacentTurn turnBounds.turn i :=
  (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
    hbad_i hbad_next).left_angle_contained

/-- Adjacent failed honest labels give the E23 adjacent-window lower bound
from an M8 window-containment package. -/
theorem honest_adjacentTurn_lower_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    Real.pi / 3 <= adjacentTurn turnBounds.turn i :=
  (honestDatum_of_m8WindowContainment_labelFailures W hi hi_next
    hbad_i hbad_next).adjacentTurn_lower

end Figure9ContainmentW12
end Swanepoel
end ErdosProblems1066

end
