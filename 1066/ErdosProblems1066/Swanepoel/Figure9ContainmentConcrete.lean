import ErdosProblems1066.Swanepoel.AngleContainmentInterface
import ErdosProblems1066.Swanepoel.M8WindowGeometryConcrete
import ErdosProblems1066.Swanepoel.Lemma10WindowGeometry

/-!
# Figure 9 adjacent-left containment projections

This module isolates the Figure 9 side of the Lemma 10 window reduction.
The inputs remain explicit: a Figure 9 distance package and a proof that the
left comparison angle is contained in the adjacent turn window.  The lemmas
below only package and project that data to the named E23 lower-bound
hypothesis.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure9ContainmentConcrete

open AngleBridgeFacts
open AngleContainmentInterface
open AngleGeometry
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open M8ConstructionInterface
open M8WindowGeometryConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Single adjacent-left witness -/

/-- If the middle turn in an adjacent three-turn window is exactly the
Figure 9 left comparison angle, then nonnegativity of the two neighboring
turns proves the concrete containment used by the Figure 9 E23 route. -/
theorem left_angle_le_adjacentTurn_of_middleTurn_eq_angle
    {turn : Nat -> Real} {i : Nat} {p qi s : Point}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (hmiddle : turn (i + 1) = angleAt p qi s) :
    angleAt p qi s <= adjacentTurn turn i := by
  rw [← hmiddle]
  unfold adjacentTurn
  exact Finset.single_le_sum (fun k _ => hnonneg k) (by simp)

/-- If the Figure 9 left comparison angle is bounded by the middle turn of an
adjacent three-turn window, then nonnegativity of the neighboring turns proves
the concrete containment used by the Figure 9 E23 route. -/
theorem left_angle_le_adjacentTurn_of_angle_le_middleTurn
    {turn : Nat -> Real} {i : Nat} {p qi s : Point}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (hangle : angleAt p qi s <= turn (i + 1)) :
    angleAt p qi s <= adjacentTurn turn i := by
  refine le_trans hangle ?_
  unfold adjacentTurn
  exact Finset.single_le_sum (fun k _ => hnonneg k) (by simp)

/-- Package Figure 9 distance data as contained data when the adjacent turn
window is realized by the left comparison angle plus nonnegative neighboring
turns. -/
def containedData_of_middleTurnAngle
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (hmiddle : turn (i + 1) = angleAt p qi s) :
    Figure9AdjacentLeftContainedData turn i where
  p := p
  qi := qi
  qj := qj
  s := s
  r := r
  distanceData := D
  left_angle_le_adjacentTurn :=
    left_angle_le_adjacentTurn_of_middleTurn_eq_angle
      hnonneg hmiddle

/-- Package explicit Figure 9 distance data and left-angle containment as the
contained-data record used by the containment interface. -/
def containedData_of_explicitDistanceContainment
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Figure9AdjacentLeftContainedData turn i where
  p := p
  qi := qi
  qj := qj
  s := s
  r := r
  distanceData := D
  left_angle_le_adjacentTurn := hcontained

/-- The local explicit Figure 9 adjacent-left data gives the adjacent turn
lower bound. -/
theorem adjacentTurn_lower_of_explicitDistanceContainment
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  adjacentTurn_lower_of_figure9DistanceData_left D hcontained

/-- Projection from contained-data form to the local adjacent turn lower
bound. -/
theorem adjacentTurn_lower_of_containedData
    {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftContainedData turn i) :
    Real.pi / 3 <= adjacentTurn turn i :=
  D.adjacentTurn_lower

/-- Forget a contained Figure 9 adjacent-left record to the existential window
geometry witness expected by `Lemma10WindowGeometry`. -/
def windowWitness_of_containedData
    {turn : Nat -> Real} {i : Nat}
    (D : Figure9AdjacentLeftContainedData turn i) :
    Exists fun p : Point =>
    Exists fun qi : Point =>
    Exists fun qj : Point =>
    Exists fun s : Point =>
    Exists fun r : Point =>
      Figure9DistanceData p qi qj s r /\
        angleAt p qi s <= adjacentTurn turn i :=
  Exists.intro D.p
    (Exists.intro D.qi
      (Exists.intro D.qj
        (Exists.intro D.s
          (Exists.intro D.r
            (And.intro D.distanceData D.left_angle_le_adjacentTurn)))))

/-! ## Uniform adjacent-left witnesses to E23 -/

/-- Uniform explicit Figure 9 adjacent-left contained witnesses for every
adjacent failed pair in the Lemma 10 window. -/
def Figure9AdjacentLeftContainedWitnesses
    (good : Nat -> Prop) (turn : Nat -> Real) : Type :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
      Figure9AdjacentLeftContainedData turn i

/-- Explicit contained witnesses supply the Figure 9 adjacent-left window
geometry predicate. -/
def leftWindowGeometry_of_containedWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainedWitnesses good turn) :
    Figure9AdjacentLeftWindowGeometry good turn := by
  intro i hi hi_next hbad_i hbad_next
  exact windowWitness_of_containedData
    (H (i := i) hi hi_next hbad_i hbad_next)

/-- The same reduction, stated directly for the window-geometry hypothesis. -/
theorem E23_of_leftWindowGeometry
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftWindowGeometry good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  figure9AdjacentWindowLowerE23_of_leftWindowGeometry H

/-- Uniform explicit Figure 9 adjacent-left contained witnesses imply the
named E23 lower-bound hypothesis. -/
theorem E23_of_containedWitnesses
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainedWitnesses good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_leftWindowGeometry
    (leftWindowGeometry_of_containedWitnesses H)

/-- A Figure 9 adjacent-left containment interface supplies the existential
window-geometry predicate through its selected contained witnesses. -/
def leftWindowGeometry_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftWindowGeometry good turn :=
  leftWindowGeometry_of_containedWitnesses
    (fun {i} hi hi_next hbad_i hbad_next =>
      H.containedData (i := i) hi hi_next hbad_i hbad_next)

/-- A Figure 9 adjacent-left containment interface implies the named E23
lower-bound hypothesis through the window-geometry route. -/
theorem E23_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_leftWindowGeometry
    (leftWindowGeometry_of_containmentInterface H)

/-! ## Atomic rows to the real containment interface -/

/-- Raw adjacent-left Figure 9 distance witnesses for every adjacent failed
pair. -/
def Figure9AdjacentLeftDistanceWitnessRows
    (good : Nat -> Prop) : Prop :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
      Exists fun p : Point =>
      Exists fun qi : Point =>
      Exists fun qj : Point =>
      Exists fun s : Point =>
      Exists fun r : Point =>
        Figure9DistanceData p qi qj s r

/-- The actual adjacent-left Figure 9 angle containment row for every
compatible distance package at an adjacent failed pair. -/
def Figure9AdjacentLeftAngleContainmentRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
    Figure9DistanceData p qi qj s r ->
      angleAt p qi s <= adjacentTurn turn i

/-- Concrete realization row: for every compatible Figure 9 distance package
at an adjacent failed pair, the left comparison angle is the middle turn of
the adjacent three-turn window. -/
def Figure9AdjacentLeftMiddleTurnAngleRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
    Figure9DistanceData p qi qj s r ->
      turn (i + 1) = angleAt p qi s

/-- Concrete comparison row: for every compatible Figure 9 distance package
at an adjacent failed pair, the left comparison angle is bounded by the middle
turn of the adjacent three-turn window. -/
def Figure9AdjacentLeftAngleLeMiddleTurnRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
    Figure9DistanceData p qi qj s r ->
      angleAt p qi s <= turn (i + 1)

/-- Project raw distance-witness rows from the real Figure 9 adjacent-left
containment interface. -/
theorem distanceWitnessRows_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftDistanceWitnessRows good := by
  intro i hi hi_next hbad_i hbad_next
  let D := H.extractedData hi hi_next hbad_i hbad_next
  exact
    Exists.intro D.p
      (Exists.intro D.qi
        (Exists.intro D.qj
          (Exists.intro D.s
            (Exists.intro D.r D.distanceData))))

/-- Project the actual left-angle containment rows from the real Figure 9
adjacent-left containment interface. -/
theorem leftAngleContainmentRows_of_containmentInterface
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftAngleContainmentRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  exact H.left_angle_le_adjacentTurn hi hi_next hbad_i hbad_next D

/-- Middle-turn angle realization rows, together with nonnegative turns,
prove the actual left-angle containment rows. -/
theorem leftAngleContainmentRows_of_middleTurnAngleRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure9AdjacentLeftMiddleTurnAngleRows good turn) :
    Figure9AdjacentLeftAngleContainmentRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  exact left_angle_le_adjacentTurn_of_middleTurn_eq_angle
    hnonneg (H hi hi_next hbad_i hbad_next D)

/-- A middle-turn upper bound for the left comparison angle, together with
nonnegative turns, proves the actual left-angle containment rows consumed by
the selected-frame Euclidean row constructor. -/
theorem leftAngleContainmentRows_of_angleLeMiddleTurnRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure9AdjacentLeftAngleLeMiddleTurnRows good turn) :
    Figure9AdjacentLeftAngleContainmentRows good turn := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  exact left_angle_le_adjacentTurn_of_angle_le_middleTurn
    hnonneg (H hi hi_next hbad_i hbad_next D)

/-- Raw adjacent-left Figure 9 distance witnesses plus the actual universal
left-angle containment row build the real containment interface. -/
def containmentInterface_of_distanceWitnessRowsAndLeftAngleContainment
    {good : Nat -> Prop} {turn : Nat -> Real}
    (distanceRows : Figure9AdjacentLeftDistanceWitnessRows good)
    (leftAngleContainment :
      Figure9AdjacentLeftAngleContainmentRows good turn) :
    Figure9AdjacentLeftContainmentInterface good turn where
  extractedData := by
    intro i hi hi_next hbad_i hbad_next
    let hp := distanceRows (i := i) hi hi_next hbad_i hbad_next
    let p := Classical.choose hp
    let hqi := Classical.choose_spec hp
    let qi := Classical.choose hqi
    let hqj := Classical.choose_spec hqi
    let qj := Classical.choose hqj
    let hs := Classical.choose_spec hqj
    let s := Classical.choose hs
    let hr := Classical.choose_spec hs
    let r := Classical.choose hr
    let D := Classical.choose_spec hr
    exact
      { p := p
        qi := qi
        qj := qj
        s := s
        r := r
        distanceData := D }
  left_angle_le_adjacentTurn := by
    intro i p qi qj s r hi hi_next hbad_i hbad_next D
    exact leftAngleContainment hi hi_next hbad_i hbad_next D

/-- Raw adjacent-left Figure 9 distance witnesses plus concrete middle-turn
angle realization rows build the real containment interface consumed by the
local window-containment constructors. -/
def containmentInterface_of_distanceWitnessRowsAndMiddleTurnAngleRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (distanceRows : Figure9AdjacentLeftDistanceWitnessRows good)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (middleTurnRows : Figure9AdjacentLeftMiddleTurnAngleRows good turn) :
    Figure9AdjacentLeftContainmentInterface good turn :=
  containmentInterface_of_distanceWitnessRowsAndLeftAngleContainment
    distanceRows
    (leftAngleContainmentRows_of_middleTurnAngleRows hnonneg middleTurnRows)

/-- The real Figure 9 adjacent-left containment interface is equivalent to
the two atomic row families: distance witnesses and left-angle containment. -/
theorem containmentInterface_nonempty_iff_distanceWitnessRows_and_leftAngleContainmentRows
    {good : Nat -> Prop} {turn : Nat -> Real} :
    Nonempty (Figure9AdjacentLeftContainmentInterface good turn) <->
      Figure9AdjacentLeftDistanceWitnessRows good /\
        Figure9AdjacentLeftAngleContainmentRows good turn := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro H =>
        exact And.intro
          (distanceWitnessRows_of_containmentInterface H)
          (leftAngleContainmentRows_of_containmentInterface H)
  case mpr =>
    intro H
    exact Nonempty.intro
      (containmentInterface_of_distanceWitnessRowsAndLeftAngleContainment
        H.1 H.2)

/-! ## Selected adjacent-left containment from failed labels -/

/-- Explicit Figure 9 adjacent-left containment data for every adjacent pair
of failed Lemma 10 comparisons. -/
structure Figure9AdjacentLeftWindowContainment
    (good : Nat -> Prop) (turn : Nat -> Real) where
  containedData :
    forall {i : Nat},
      1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
        Figure9AdjacentLeftContainedData turn i

namespace Figure9AdjacentLeftWindowContainment

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- The selected Figure 9 contained witness at one adjacent bad pair. -/
def data (H : Figure9AdjacentLeftWindowContainment good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Figure9AdjacentLeftContainedData turn i :=
  H.containedData hi hi_next hbad_i hbad_next

/-- Project the selected raw Figure 9 distance witness. -/
def extractedData (H : Figure9AdjacentLeftWindowContainment good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Figure9AdjacentExtractedData where
  p := (H.data hi hi_next hbad_i hbad_next).p
  qi := (H.data hi hi_next hbad_i hbad_next).qi
  qj := (H.data hi hi_next hbad_i hbad_next).qj
  s := (H.data hi hi_next hbad_i hbad_next).s
  r := (H.data hi hi_next hbad_i hbad_next).r
  distanceData := (H.data hi hi_next hbad_i hbad_next).distanceData

/-- Project the selected Figure 9 distance data. -/
theorem distanceData (H : Figure9AdjacentLeftWindowContainment good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Figure9DistanceData
      (H.data hi hi_next hbad_i hbad_next).p
      (H.data hi hi_next hbad_i hbad_next).qi
      (H.data hi hi_next hbad_i hbad_next).qj
      (H.data hi hi_next hbad_i hbad_next).s
      (H.data hi hi_next hbad_i hbad_next).r :=
  (H.data hi hi_next hbad_i hbad_next).distanceData

/-- Project the selected left-angle containment. -/
theorem left_angle_le_adjacentTurn
    (H : Figure9AdjacentLeftWindowContainment good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    angleAt
        (H.data hi hi_next hbad_i hbad_next).p
        (H.data hi hi_next hbad_i hbad_next).qi
        (H.data hi hi_next hbad_i hbad_next).s <=
      adjacentTurn turn i :=
  (H.data hi hi_next hbad_i hbad_next).left_angle_le_adjacentTurn

/-- The selected Figure 9 distance data gives the left-angle lower bound. -/
theorem left_angle_lower
    (H : Figure9AdjacentLeftWindowContainment good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Real.pi / 3 <=
      angleAt
        (H.data hi hi_next hbad_i hbad_next).p
        (H.data hi hi_next hbad_i hbad_next).qi
        (H.data hi hi_next hbad_i hbad_next).s :=
  figure9LeftAngle_lower_of_distanceData
    (H.distanceData hi hi_next hbad_i hbad_next)

/-- The selected Figure 9 distance and containment data gives the local E23
turn-window lower bound. -/
theorem adjacentTurn_lower
    (H : Figure9AdjacentLeftWindowContainment good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Real.pi / 3 <= adjacentTurn turn i :=
  (H.data hi hi_next hbad_i hbad_next).adjacentTurn_lower

/-- Forget selected containment data to the uniform contained-witness
predicate. -/
def toContainedWitnesses
    (H : Figure9AdjacentLeftWindowContainment good turn) :
    Figure9AdjacentLeftContainedWitnesses good turn :=
  fun {_i} hi hi_next hbad_i hbad_next =>
    H.data hi hi_next hbad_i hbad_next

/-- Forget explicit selected data to the existential Figure 9 left-window
geometry predicate used by `Lemma10WindowGeometry`. -/
def toWindowGeometry
    (H : Figure9AdjacentLeftWindowContainment good turn) :
    Figure9AdjacentLeftWindowGeometry good turn :=
  leftWindowGeometry_of_containedWitnesses H.toContainedWitnesses

/-- Reduction from explicit Figure 9 adjacent-left containment to E23. -/
theorem E23
    (H : Figure9AdjacentLeftWindowContainment good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  E23_of_containedWitnesses H.toContainedWitnesses

/-- Direct pointwise form of the E23 reduction. -/
theorem E23_apply
    (H : Figure9AdjacentLeftWindowContainment good turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Real.pi / 3 <= adjacentTurn turn i :=
  H.E23 hi hi_next hbad_i hbad_next

/-- E23 as the raw adjacent-failures turn-force interface. -/
theorem adjacentFailuresForceTurn
    (H : Figure9AdjacentLeftWindowContainment good turn) :
    AdjacentFailuresForceTurn good turn :=
  adjacentFailuresForceTurn_of_E23 H.E23

/-- Convert uniform contained witnesses to the selected-window facade. -/
def ofContainedWitnesses
    (H : Figure9AdjacentLeftContainedWitnesses good turn) :
    Figure9AdjacentLeftWindowContainment good turn where
  containedData := by
    intro i hi hi_next hbad_i hbad_next
    exact H (i := i) hi hi_next hbad_i hbad_next

/-- Convert the stronger uniform interface from `AngleContainmentInterface` to
the selected-data facade in this module. -/
def ofContainmentInterface
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftWindowContainment good turn where
  containedData := by
    intro i hi hi_next hbad_i hbad_next
    exact H.containedData hi hi_next hbad_i hbad_next

/-- The Figure 9 containment interface reduces to E23 through the selected
window-geometry facade. -/
theorem E23_of_containmentInterface
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  (ofContainmentInterface H).E23

end Figure9AdjacentLeftWindowContainment

/-! ## Honest M8 projections -/

/-- Honest M8 specialization of the explicit contained-witness predicate. -/
abbrev HonestFigure9AdjacentLeftContainedWitnesses
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) :=
  Figure9AdjacentLeftContainedWitnesses
    (M8BrokenLatticeGood P.data) turn

/-- Honest M8 contained witnesses supply the Figure 9 adjacent-left window
geometry predicate. -/
def honestLeftWindowGeometry_of_containedWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftContainedWitnesses P turn) :
    HonestFigure9AdjacentLeftWindowGeometry P turn :=
  @leftWindowGeometry_of_containedWitnesses
    (M8BrokenLatticeGood P.data) turn H

/-- Honest M8 contained witnesses imply the named E23 lower-bound hypothesis. -/
theorem honestE23_of_containedWitnesses
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftContainedWitnesses P turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry
    (honestLeftWindowGeometry_of_containedWitnesses H)

/-- Honest M8 Figure 9 adjacent-left containment implies the named E23
lower-bound hypothesis. -/
theorem honestE23_of_containmentInterface
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood P.data) turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry
    (leftWindowGeometry_of_containmentInterface H)

/-- Figure 9 adjacent-left containment specialized to the local `m = 8`
predicate package. -/
def M8Figure9AdjacentLeftWindowContainment
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Type :=
  Figure9AdjacentLeftWindowContainment (M8BrokenLatticeGood P) turn

/-- Figure 9 adjacent-left containment specialized to an honest local `m = 8`
package. -/
def HonestFigure9AdjacentLeftWindowContainment
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Type :=
  M8Figure9AdjacentLeftWindowContainment P.data turn

/-- Explicit `m = 8` Figure 9 containment gives the local E23 hypothesis. -/
theorem m8Figure9AdjacentWindowLowerE23_of_containment
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure9AdjacentLeftWindowContainment P turn) :
    M8Figure9AdjacentWindowLowerE23 P turn :=
  H.E23

/-- Explicit honest Figure 9 containment gives the honest E23 hypothesis. -/
theorem honestFigure9AdjacentWindowLowerE23_of_containment
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  H.E23

/-- Explicit `m = 8` Figure 9 containment gives the raw adjacent-failures
turn-force interface. -/
theorem m8AdjacentFailuresForceTurn_of_containment
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure9AdjacentLeftWindowContainment P turn) :
    AdjacentFailuresForceTurn (M8BrokenLatticeGood P) turn :=
  H.adjacentFailuresForceTurn

/-- Explicit honest Figure 9 containment gives the raw adjacent-failures
turn-force interface. -/
theorem honestAdjacentFailuresForceTurn_of_containment
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn) :
    AdjacentFailuresForceTurn (M8BrokenLatticeGood P.data) turn :=
  H.adjacentFailuresForceTurn

/-- A failed honest label equality is a failed named local comparison. -/
theorem not_m8BrokenLatticeGood_of_not_m8LabelGood
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {i : Nat}
    (hbad : Not (M8LabelGood P.data.labels i)) :
    Not (M8BrokenLatticeGood P.data i) := by
  intro hgood
  exact hbad ((P.good_iff_labelGood i).1 hgood)

/-- Select honest Figure 9 contained data from adjacent failed label
equalities. -/
def honestContainedData_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Figure9AdjacentLeftContainedData turn i :=
  H.data hi hi_next
    (not_m8BrokenLatticeGood_of_not_m8LabelGood hbad_i)
    (not_m8BrokenLatticeGood_of_not_m8LabelGood hbad_next)

/-- Project the raw Figure 9 distance witness selected by adjacent failed
label equalities. -/
def honestExtractedData_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Figure9AdjacentExtractedData :=
  H.extractedData hi hi_next
    (not_m8BrokenLatticeGood_of_not_m8LabelGood hbad_i)
    (not_m8BrokenLatticeGood_of_not_m8LabelGood hbad_next)

/-- Project the concrete Figure 9 distance package selected by adjacent failed
label equalities. -/
theorem honestDistanceData_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Figure9DistanceData
      (honestContainedData_of_labelFailures H hi hi_next
        hbad_i hbad_next).p
      (honestContainedData_of_labelFailures H hi hi_next
        hbad_i hbad_next).qi
      (honestContainedData_of_labelFailures H hi hi_next
        hbad_i hbad_next).qj
      (honestContainedData_of_labelFailures H hi hi_next
        hbad_i hbad_next).s
      (honestContainedData_of_labelFailures H hi hi_next
        hbad_i hbad_next).r :=
  (honestContainedData_of_labelFailures H hi hi_next
    hbad_i hbad_next).distanceData

/-- Project the left-angle containment selected by adjacent failed label
equalities. -/
theorem honest_left_angle_le_adjacentTurn_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    angleAt
        (honestContainedData_of_labelFailures H hi hi_next
          hbad_i hbad_next).p
        (honestContainedData_of_labelFailures H hi hi_next
          hbad_i hbad_next).qi
        (honestContainedData_of_labelFailures H hi hi_next
          hbad_i hbad_next).s <=
      adjacentTurn turn i :=
  (honestContainedData_of_labelFailures H hi hi_next
    hbad_i hbad_next).left_angle_le_adjacentTurn

/-- Adjacent failed label equalities force the honest Figure 9 E23 lower
bound pointwise. -/
theorem honestAdjacentTurn_lower_of_labelFailures
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowContainment P turn)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8LabelGood P.data.labels i))
    (hbad_next : Not (M8LabelGood P.data.labels (i + 1))) :
    Real.pi / 3 <= adjacentTurn turn i :=
  (honestContainedData_of_labelFailures H hi hi_next
    hbad_i hbad_next).adjacentTurn_lower

/-- Projection of the Figure 9 E23 field from the concrete M8 window
containment package. -/
theorem honestE23_of_windowContainment
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  honestFigure9_E23_of_containment W

/-- Projection of the Figure 9 E23 field from separately supplied concrete
M8 Figure 8 and Figure 9 containment interfaces. -/
theorem honestE23_of_containmentInterfaces
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  honestFigure9_E23_of_containmentInterfaces
    (localLabels := localLabels) (turnBounds := turnBounds)
    figure8 figure9_left

/-! ## Projections from the existing M8 window-containment package -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- The Figure 9 field of an M8 window-containment package as explicit
selected adjacent-left containment. -/
def honestContainment_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentLeftWindowContainment
      localLabels.predicates turnBounds.turn :=
  Figure9AdjacentLeftWindowContainment.ofContainmentInterface W.figure9_left

/-- Select Figure 9 contained data from an M8 window-containment package using
adjacent failed label equalities. -/
def honestContainedData_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    Figure9AdjacentLeftContainedData turnBounds.turn i :=
  honestContainedData_of_labelFailures
    (honestContainment_of_m8WindowContainment W)
    hi hi_next hbad_i hbad_next

/-- Project the raw Figure 9 distance witness from an M8 window-containment
package using adjacent failed label equalities. -/
def honestExtractedData_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    Figure9AdjacentExtractedData :=
  honestExtractedData_of_labelFailures
    (honestContainment_of_m8WindowContainment W)
    hi hi_next hbad_i hbad_next

/-- Project the concrete Figure 9 distance package from an M8
window-containment package using adjacent failed label equalities. -/
theorem honestDistanceData_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    Figure9DistanceData
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hi_next hbad_i hbad_next).p
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hi_next hbad_i hbad_next).qi
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hi_next hbad_i hbad_next).qj
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hi_next hbad_i hbad_next).s
      (honestContainedData_of_m8WindowContainment_labelFailures W
        hi hi_next hbad_i hbad_next).r :=
  (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hi_next hbad_i hbad_next).distanceData

/-- Project the selected left-angle containment from an M8 window-containment
package using adjacent failed label equalities. -/
theorem honest_left_angle_le_adjacentTurn_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    angleAt
        (honestContainedData_of_m8WindowContainment_labelFailures W
          hi hi_next hbad_i hbad_next).p
        (honestContainedData_of_m8WindowContainment_labelFailures W
          hi hi_next hbad_i hbad_next).qi
        (honestContainedData_of_m8WindowContainment_labelFailures W
          hi hi_next hbad_i hbad_next).s <=
      adjacentTurn turnBounds.turn i :=
  (honestContainedData_of_m8WindowContainment_labelFailures W
    hi hi_next hbad_i hbad_next).left_angle_le_adjacentTurn

/-- Projection to honest E23 through the Figure 9-only containment facade. -/
theorem honestFigure9AdjacentWindowLowerE23_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  (honestContainment_of_m8WindowContainment W).E23

/-- Projection to the raw adjacent-failures turn-force interface through the
Figure 9-only containment facade. -/
theorem honestAdjacentFailuresForceTurn_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    AdjacentFailuresForceTurn
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  (honestContainment_of_m8WindowContainment W).adjacentFailuresForceTurn

/-- Pointwise honest E23 projection from an M8 window-containment package. -/
theorem honestFigure9AdjacentWindowLowerE23_apply_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1))) :
    Real.pi / 3 <= adjacentTurn turnBounds.turn i :=
  honestFigure9AdjacentWindowLowerE23_of_m8WindowContainment W
    hi hi_next hbad_i hbad_next

/-- Pointwise honest E23 projection from an M8 window-containment package,
stated for failed label equalities. -/
theorem honestFigure9AdjacentWindowLowerE23_apply_of_m8WindowContainment_labelFailures
    (W : M8WindowContainment localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (M8LabelGood localLabels.predicates.data.labels i))
    (hbad_next :
      Not (M8LabelGood localLabels.predicates.data.labels (i + 1))) :
    Real.pi / 3 <= adjacentTurn turnBounds.turn i :=
  honestAdjacentTurn_lower_of_labelFailures
    (honestContainment_of_m8WindowContainment W)
    hi hi_next hbad_i hbad_next

/-- The same M8 E23 projection, routed through
`M8WindowGeometryConcrete`. -/
theorem honestFigure9AdjacentWindowLowerE23_of_m8WindowContainment_concrete
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  M8WindowGeometryConcrete.honestFigure9_E23_of_containment W

end Figure9ContainmentConcrete
end Swanepoel
end ErdosProblems1066

end
