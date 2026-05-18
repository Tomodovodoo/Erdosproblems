import ErdosProblems1066.Swanepoel.AngleGeometry
import ErdosProblems1066.Swanepoel.Lemma10EuclideanBridge

/-!
Window-level geometry helpers for Swanepoel Lemma 10.

The bridge modules name E22 and E23 as turn-window lower bounds.  This file
keeps the next reduction honest: the hypotheses below are local distance data
plus an explicit containment of the resulting geometric angle in the relevant
turn window.  No paper-level estimate is introduced as a field.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma10WindowGeometry

open AngleBridgeFacts
open AngleGeometry
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10EuclideanBridge
open Lemma10Inequalities
open LocalConfigurations
open TriangleAngleFacts

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! Unit-distance angle facts routed directly to window lower bounds. -/

lemma angleAt_lower_of_sqDist_unit_base
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hbase : 1 <= sqDist a c) :
    Real.pi / 3 <= angleAt a b c :=
  pi_div_three_le_angleAt_of_unit_sides_sqDist_ge_one hab hcb hbase

lemma angleAt_lower_of_eucUnit_base
    {a b c : Point}
    (hab : EucUnit a b) (hcb : EucUnit c b)
    (hbase : EucSeparated a c) :
    Real.pi / 3 <= angleAt a b c :=
  pi_div_three_le_angleAt_of_eucUnit_sides_eucSeparated_base
    hab hcb hbase

lemma separatedTurn_lower_of_sqDist_unit_base
    {turn : Nat -> Real} {i j : Nat} {a b c : Point}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hbase : 1 <= sqDist a c)
    (hcontained : angleAt a b c <= separatedTurn turn i j) :
    Real.pi / 3 <= separatedTurn turn i j := by
  exact le_trans
    (angleAt_lower_of_sqDist_unit_base hab hcb hbase)
    hcontained

lemma adjacentTurn_lower_of_sqDist_unit_base
    {turn : Nat -> Real} {i : Nat} {a b c : Point}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hbase : 1 <= sqDist a c)
    (hcontained : angleAt a b c <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i := by
  exact le_trans
    (angleAt_lower_of_sqDist_unit_base hab hcb hbase)
    hcontained

lemma separatedTurn_lower_of_eucUnit_base
    {turn : Nat -> Real} {i j : Nat} {a b c : Point}
    (hab : EucUnit a b) (hcb : EucUnit c b)
    (hbase : EucSeparated a c)
    (hcontained : angleAt a b c <= separatedTurn turn i j) :
    Real.pi / 3 <= separatedTurn turn i j := by
  exact le_trans
    (angleAt_lower_of_eucUnit_base hab hcb hbase)
    hcontained

lemma adjacentTurn_lower_of_eucUnit_base
    {turn : Nat -> Real} {i : Nat} {a b c : Point}
    (hab : EucUnit a b) (hcb : EucUnit c b)
    (hbase : EucSeparated a c)
    (hcontained : angleAt a b c <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i := by
  exact le_trans
    (angleAt_lower_of_eucUnit_base hab hcb hbase)
    hcontained

/-! Figure 8 and Figure 9 distance data give concrete window lower bounds. -/

lemma figure8CentralAngle_lower_of_distanceData
    {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r) :
    Real.pi / 3 <= angleAt qi p qj :=
  angleAt_lower_of_eucUnit_base
    (eucUnit_comm D.p_qi)
    (eucUnit_comm D.p_qj)
    D.qi_qj_sep

lemma separatedTurn_lower_of_figure8DistanceData
    {turn : Nat -> Real} {i j : Nat} {p qi qj s r : Point}
    (D : Figure8DistanceData p qi qj s r)
    (hcontained : angleAt qi p qj <= separatedTurn turn i j) :
    Real.pi / 3 <= separatedTurn turn i j := by
  exact le_trans
    (figure8CentralAngle_lower_of_distanceData D)
    hcontained

lemma figure9CentralAngle_lower_of_distanceData
    {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    Real.pi / 3 <= angleAt qi p qj :=
  angleAt_lower_of_eucUnit_base
    (eucUnit_comm D.p_qi)
    (eucUnit_comm D.p_qj)
    D.qi_qj_sep

lemma figure9LeftAngle_lower_of_distanceData
    {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    Real.pi / 3 <= angleAt p qi s :=
  angleAt_lower_of_eucUnit_base
    D.p_qi
    (eucUnit_comm D.qi_s)
    D.p_s_sep

lemma figure9RightAngle_lower_of_distanceData
    {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r) :
    Real.pi / 3 <= angleAt p qj r :=
  angleAt_lower_of_eucUnit_base
    D.p_qj
    (eucUnit_comm D.qj_r)
    D.p_r_sep

lemma adjacentTurn_lower_of_figure9DistanceData_central
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt qi p qj <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i := by
  exact le_trans
    (figure9CentralAngle_lower_of_distanceData D)
    hcontained

lemma adjacentTurn_lower_of_figure9DistanceData_left
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qi s <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i := by
  exact le_trans
    (figure9LeftAngle_lower_of_distanceData D)
    hcontained

lemma adjacentTurn_lower_of_figure9DistanceData_right
    {turn : Nat -> Real} {i : Nat} {p qi qj s r : Point}
    (D : Figure9DistanceData p qi qj s r)
    (hcontained : angleAt p qj r <= adjacentTurn turn i) :
    Real.pi / 3 <= adjacentTurn turn i := by
  exact le_trans
    (figure9RightAngle_lower_of_distanceData D)
    hcontained

/-! Per-window witness hypotheses for E22 and E23. -/

def Figure8SeparatedWindowGeometry
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i j : Nat},
    1 <= i -> i + 1 < j -> j <= 10 ->
      Not (good i) -> Not (good j) ->
        Exists fun p : Point =>
        Exists fun qi : Point =>
        Exists fun qj : Point =>
        Exists fun s : Point =>
        Exists fun r : Point =>
          Figure8DistanceData p qi qj s r /\
            angleAt qi p qj <= separatedTurn turn i j

theorem figure8SeparatedWindowLowerE22_of_windowGeometry
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedWindowGeometry good turn) :
    Figure8SeparatedWindowLowerE22 good turn := by
  intro i j hi hsep hj hbad_i hbad_j
  match H hi hsep hj hbad_i hbad_j with
  | Exists.intro p hp =>
    match hp with
    | Exists.intro qi hqi =>
      match hqi with
      | Exists.intro qj hqj =>
        match hqj with
        | Exists.intro s hs =>
          match hs with
          | Exists.intro r hr =>
            exact separatedTurn_lower_of_figure8DistanceData
              hr.1 hr.2

def Figure9AdjacentCentralWindowGeometry
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
        Exists fun p : Point =>
        Exists fun qi : Point =>
        Exists fun qj : Point =>
        Exists fun s : Point =>
        Exists fun r : Point =>
          Figure9DistanceData p qi qj s r /\
            angleAt qi p qj <= adjacentTurn turn i

def Figure9AdjacentLeftWindowGeometry
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
        Exists fun p : Point =>
        Exists fun qi : Point =>
        Exists fun qj : Point =>
        Exists fun s : Point =>
        Exists fun r : Point =>
          Figure9DistanceData p qi qj s r /\
            angleAt p qi s <= adjacentTurn turn i

def Figure9AdjacentRightWindowGeometry
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
      Not (good i) -> Not (good (i + 1)) ->
        Exists fun p : Point =>
        Exists fun qi : Point =>
        Exists fun qj : Point =>
        Exists fun s : Point =>
        Exists fun r : Point =>
          Figure9DistanceData p qi qj s r /\
            angleAt p qj r <= adjacentTurn turn i

theorem figure9AdjacentWindowLowerE23_of_centralWindowGeometry
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentCentralWindowGeometry good turn) :
    Figure9AdjacentWindowLowerE23 good turn := by
  intro i hi hi_next hbad_i hbad_next
  match H hi hi_next hbad_i hbad_next with
  | Exists.intro p hp =>
    match hp with
    | Exists.intro qi hqi =>
      match hqi with
      | Exists.intro qj hqj =>
        match hqj with
        | Exists.intro s hs =>
          match hs with
          | Exists.intro r hr =>
            exact adjacentTurn_lower_of_figure9DistanceData_central
              hr.1 hr.2

theorem figure9AdjacentWindowLowerE23_of_leftWindowGeometry
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftWindowGeometry good turn) :
    Figure9AdjacentWindowLowerE23 good turn := by
  intro i hi hi_next hbad_i hbad_next
  match H hi hi_next hbad_i hbad_next with
  | Exists.intro p hp =>
    match hp with
    | Exists.intro qi hqi =>
      match hqi with
      | Exists.intro qj hqj =>
        match hqj with
        | Exists.intro s hs =>
          match hs with
          | Exists.intro r hr =>
            exact adjacentTurn_lower_of_figure9DistanceData_left
              hr.1 hr.2

theorem figure9AdjacentWindowLowerE23_of_rightWindowGeometry
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentRightWindowGeometry good turn) :
    Figure9AdjacentWindowLowerE23 good turn := by
  intro i hi hi_next hbad_i hbad_next
  match H hi hi_next hbad_i hbad_next with
  | Exists.intro p hp =>
    match hp with
    | Exists.intro qi hqi =>
      match hqi with
      | Exists.intro qj hqj =>
        match hqj with
        | Exists.intro s hs =>
          match hs with
          | Exists.intro r hr =>
            exact adjacentTurn_lower_of_figure9DistanceData_right
              hr.1 hr.2

theorem E22_E23_of_leftWindowGeometry
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H8 : Figure8SeparatedWindowGeometry good turn)
    (H9 : Figure9AdjacentLeftWindowGeometry good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  And.intro
    (figure8SeparatedWindowLowerE22_of_windowGeometry H8)
    (figure9AdjacentWindowLowerE23_of_leftWindowGeometry H9)

/-! Specializations to the local m equals 8 and honest packages. -/

def M8Figure8SeparatedWindowGeometry
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Prop :=
  Figure8SeparatedWindowGeometry (M8BrokenLatticeGood P) turn

def M8Figure9AdjacentLeftWindowGeometry
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) (turn : Nat -> Real) : Prop :=
  Figure9AdjacentLeftWindowGeometry (M8BrokenLatticeGood P) turn

theorem m8Figure8SeparatedWindowLowerE22_of_windowGeometry
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure8SeparatedWindowGeometry P turn) :
    M8Figure8SeparatedWindowLowerE22 P turn :=
  figure8SeparatedWindowLowerE22_of_windowGeometry H

theorem m8Figure9AdjacentWindowLowerE23_of_leftWindowGeometry
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H : M8Figure9AdjacentLeftWindowGeometry P turn) :
    M8Figure9AdjacentWindowLowerE23 P turn :=
  figure9AdjacentWindowLowerE23_of_leftWindowGeometry H

theorem m8E22_E23_of_leftWindowGeometry
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8} {turn : Nat -> Real}
    (H8 : M8Figure8SeparatedWindowGeometry P turn)
    (H9 : M8Figure9AdjacentLeftWindowGeometry P turn) :
    M8Figure8SeparatedWindowLowerE22 P turn /\
      M8Figure9AdjacentWindowLowerE23 P turn :=
  And.intro
    (m8Figure8SeparatedWindowLowerE22_of_windowGeometry H8)
    (m8Figure9AdjacentWindowLowerE23_of_leftWindowGeometry H9)

def HonestFigure8SeparatedWindowGeometry
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Prop :=
  M8Figure8SeparatedWindowGeometry P.data turn

def HonestFigure9AdjacentLeftWindowGeometry
    {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) (turn : Nat -> Real) : Prop :=
  M8Figure9AdjacentLeftWindowGeometry P.data turn

theorem honestFigure8SeparatedWindowLowerE22_of_windowGeometry
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8SeparatedWindowGeometry P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn :=
  m8Figure8SeparatedWindowLowerE22_of_windowGeometry H

theorem honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure9AdjacentLeftWindowGeometry P turn) :
    HonestFigure9AdjacentWindowLowerE23 P turn :=
  m8Figure9AdjacentWindowLowerE23_of_leftWindowGeometry H

theorem honestE22_E23_of_leftWindowGeometry
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H8 : HonestFigure8SeparatedWindowGeometry P turn)
    (H9 : HonestFigure9AdjacentLeftWindowGeometry P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn /\
      HonestFigure9AdjacentWindowLowerE23 P turn :=
  And.intro
    (honestFigure8SeparatedWindowLowerE22_of_windowGeometry H8)
    (honestFigure9AdjacentWindowLowerE23_of_leftWindowGeometry H9)

end Lemma10WindowGeometry
end Swanepoel
end ErdosProblems1066

end
