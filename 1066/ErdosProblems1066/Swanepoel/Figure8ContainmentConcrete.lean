import ErdosProblems1066.Swanepoel.AngleContainmentInterface
import ErdosProblems1066.Swanepoel.Lemma10WindowGeometry
import ErdosProblems1066.Swanepoel.M8WindowGeometryConcrete

set_option autoImplicit false

/-!
# Concrete Figure 8 containment projections

This module isolates the Figure 8 side of the separated-window containment
route.  Its inputs are explicit distance data plus the central-angle
containment in the separated turn window; its outputs are the generic and
honest `m = 8` E22 lower-bound hypotheses.

No new Euclidean estimate is introduced here.  The only inequality step is the
checked unit-distance angle lower bound from `Lemma10WindowGeometry`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure8ContainmentConcrete

open AngleContainmentInterface
open AngleBridgeFacts
open AngleGeometry
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open M8ConstructionInterface
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Generic separated-window Figure 8 containment -/

/-- Explicit Figure 8 distance data and central-angle containment for every
separated pair of failed Lemma 10 comparisons. -/
structure Figure8SeparatedWindowContainment
    (good : Nat -> Prop) (turn : Nat -> Real) where
  containedData :
    forall {i j : Nat},
      1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
        Figure8SeparatedContainedData turn i j

namespace Figure8SeparatedWindowContainment

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- The selected Figure 8 contained witness at one separated bad pair. -/
def data (H : Figure8SeparatedWindowContainment good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Figure8SeparatedContainedData turn i j :=
  H.containedData hi hsep hj hbad_i hbad_j

/-- Project the selected raw Figure 8 distance witness. -/
def extractedData (H : Figure8SeparatedWindowContainment good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Figure8SeparatedExtractedData where
  p := (H.data hi hsep hj hbad_i hbad_j).p
  qi := (H.data hi hsep hj hbad_i hbad_j).qi
  qj := (H.data hi hsep hj hbad_i hbad_j).qj
  s := (H.data hi hsep hj hbad_i hbad_j).s
  r := (H.data hi hsep hj hbad_i hbad_j).r
  distanceData := (H.data hi hsep hj hbad_i hbad_j).distanceData

/-- Project the selected Figure 8 distance data. -/
theorem distanceData (H : Figure8SeparatedWindowContainment good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Figure8DistanceData
      (H.data hi hsep hj hbad_i hbad_j).p
      (H.data hi hsep hj hbad_i hbad_j).qi
      (H.data hi hsep hj hbad_i hbad_j).qj
      (H.data hi hsep hj hbad_i hbad_j).s
      (H.data hi hsep hj hbad_i hbad_j).r :=
  (H.data hi hsep hj hbad_i hbad_j).distanceData

/-- Project the selected central-angle containment. -/
theorem central_angle_le_separatedTurn
    (H : Figure8SeparatedWindowContainment good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    angleAt
        (H.data hi hsep hj hbad_i hbad_j).qi
        (H.data hi hsep hj hbad_i hbad_j).p
        (H.data hi hsep hj hbad_i hbad_j).qj <=
      separatedTurn turn i j :=
  (H.data hi hsep hj hbad_i hbad_j).central_angle_le_separatedTurn

/-- The selected Figure 8 distance data gives the central-angle lower bound. -/
theorem central_angle_lower
    (H : Figure8SeparatedWindowContainment good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Real.pi / 3 <=
      angleAt
        (H.data hi hsep hj hbad_i hbad_j).qi
        (H.data hi hsep hj hbad_i hbad_j).p
        (H.data hi hsep hj hbad_i hbad_j).qj :=
  figure8CentralAngle_lower_of_distanceData
    (H.distanceData hi hsep hj hbad_i hbad_j)

/-- The selected Figure 8 distance and containment data gives the local E22
turn-window lower bound. -/
theorem separatedTurn_lower
    (H : Figure8SeparatedWindowContainment good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Real.pi / 3 <= separatedTurn turn i j :=
  (H.data hi hsep hj hbad_i hbad_j).separatedTurn_lower

/-- Forget explicit selected data to the existential Figure 8 window geometry
predicate used by `Lemma10WindowGeometry`. -/
def toWindowGeometry
    (H : Figure8SeparatedWindowContainment good turn) :
    Figure8SeparatedWindowGeometry good turn := by
  intro i j hi hsep hj hbad_i hbad_j
  let D := H.data hi hsep hj hbad_i hbad_j
  exact
    Exists.intro D.p
      (Exists.intro D.qi
        (Exists.intro D.qj
          (Exists.intro D.s
            (Exists.intro D.r
              (And.intro D.distanceData
                D.central_angle_le_separatedTurn)))))

/-- Reduction from explicit Figure 8 separated-window containment to E22. -/
theorem E22
    (H : Figure8SeparatedWindowContainment good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  figure8SeparatedWindowLowerE22_of_windowGeometry H.toWindowGeometry

/-- Direct pointwise form of the E22 reduction. -/
theorem E22_apply
    (H : Figure8SeparatedWindowContainment good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Real.pi / 3 <= separatedTurn turn i j :=
  H.E22 hi hsep hj hbad_i hbad_j

/-- Convert the stronger uniform interface from `AngleContainmentInterface` to
the selected-data facade in this module. -/
def ofContainmentInterface
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowContainment good turn where
  containedData := by
    intro i j hi hsep hj hbad_i hbad_j
    exact H.containedData hi hsep hj hbad_i hbad_j

/-- The Figure 8 containment interface reduces to E22 through the selected
window-geometry facade. -/
theorem E22_of_containmentInterface
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  (ofContainmentInterface H).E22

end Figure8SeparatedWindowContainment

/-! ## `m = 8` specializations -/

/-- Figure 8 separated-window containment specialized to the local `m = 8`
predicate package. -/
def M8Figure8SeparatedWindowContainment
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Type :=
  Figure8SeparatedWindowContainment (M8BrokenLatticeGood P) turn

/-- Figure 8 separated-window containment specialized to an honest local
`m = 8` package. -/
def HonestFigure8SeparatedWindowContainment
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Type :=
  M8Figure8SeparatedWindowContainment P.data turn

/-- Explicit `m = 8` Figure 8 containment gives the local E22 hypothesis. -/
theorem m8Figure8SeparatedWindowLowerE22_of_containment
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure8SeparatedWindowContainment P turn) :
    M8Figure8SeparatedWindowLowerE22 P turn :=
  H.E22

/-- Explicit honest Figure 8 containment gives the honest E22 hypothesis. -/
theorem honestFigure8SeparatedWindowLowerE22_of_containment
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowContainment P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn :=
  H.E22

/-! ## Projections from the existing M8 window-containment package -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- The Figure 8 field of an M8 window-containment package as explicit
selected separated-window containment. -/
def honestContainment_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowContainment
      localLabels.predicates turnBounds.turn :=
  Figure8SeparatedWindowContainment.ofContainmentInterface W.figure8

/-- Projection to E22 through the Figure 8-only facade. -/
theorem honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  (honestContainment_of_m8WindowContainment W).E22

/-- The same M8 E22 projection, routed through
`M8WindowGeometryConcrete`. -/
theorem honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment_concrete
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  M8WindowGeometryConcrete.honestFigure8_E22_of_containment W

end Figure8ContainmentConcrete
end Swanepoel
end ErdosProblems1066

end
