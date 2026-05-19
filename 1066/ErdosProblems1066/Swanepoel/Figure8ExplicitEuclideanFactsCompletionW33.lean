import ErdosProblems1066.Swanepoel.Figure8EuclideanFactsConcrete
import ErdosProblems1066.Swanepoel.M8WindowGeometryFromContainment

set_option autoImplicit false

/-!
# W33 completion for explicit Figure 8 Euclidean facts

This module keeps the Figure 8 route parallel to the explicit Figure 9 route:
the explicit package yields Prop-level selected distance data carrying
central-angle containment, and E22 is derived from those selected facts.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure8EuclideanFactsConcrete

open AngleContainmentInterface
open AngleBridgeFacts
open AngleGeometry
open Figure8ContainmentConcrete
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open LocalConfigurations
open M8ConstructionInterface
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

namespace Figure8ExplicitEuclideanFacts

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-! ## Turn-window reductions for the remaining Figure 8 angle row -/

/-- A local Figure 8 central-angle turn-window source: the central angle is
bounded by the sum of turns on some subwindow of the separated interval
`i + 1, ..., j`.

This is the strongest useful local reduction currently available without
inventing geometry.  A future geometric proof may produce the subwindow by a
cyclic-order/telescope argument; nonnegativity of the remaining turn slots then
embeds that subwindow into `separatedTurn`. -/
def CentralAngleTurnSubwindow
    (turn : Nat -> Real) (i j : Nat) (p qi qj : Point) : Prop :=
  Exists fun window : Finset Nat =>
    window <= Finset.Icc (i + 1) j /\
      angleAt qi p qj <= window.sum turn

/-- Exact local Figure 8 telescope source: the central angle is exactly the
sum of turns on a subwindow of the separated interval. -/
def CentralAngleTurnSubwindowEq
    (turn : Nat -> Real) (i j : Nat) (p qi qj : Point) : Prop :=
  Exists fun window : Finset Nat =>
    window <= Finset.Icc (i + 1) j /\
      angleAt qi p qj = window.sum turn

/-! ### Reusable subwindow arithmetic -/

/-- A nonnegative turn subwindow inside `Finset.Icc (i + 1) j` is bounded by
the separated turn window.  The nonnegativity hypothesis is local to the
containing separated interval. -/
theorem turnSubwindow_sum_le_separatedTurn
    {turn : Nat -> Real} {i j : Nat} {window : Finset Nat}
    (hsub : window <= Finset.Icc (i + 1) j)
    (hnonneg :
      forall k : Nat, k ∈ Finset.Icc (i + 1) j -> 0 <= turn k) :
    window.sum turn <= separatedTurn turn i j := by
  simpa [separatedTurn] using
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k hk _hnot => hnonneg k hk)

/-- Global pointwise turn nonnegativity gives the subwindow comparison used
by the M8 turn-bound packages. -/
theorem turnSubwindow_sum_le_separatedTurn_of_nonneg
    {turn : Nat -> Real} {i j : Nat} {window : Finset Nat}
    (hsub : window <= Finset.Icc (i + 1) j)
    (hnonneg : forall k : Nat, 0 <= turn k) :
    window.sum turn <= separatedTurn turn i j :=
  turnSubwindow_sum_le_separatedTurn hsub
    (fun k _hk => hnonneg k)

/-- Interval subwindows are ordinary subwindows of the separated turn
window. -/
theorem turnSubwindowIcc_sum_le_separatedTurn
    {turn : Nat -> Real} {i j a b : Nat}
    (ha : i + 1 <= a) (hb : b <= j)
    (hnonneg :
      forall k : Nat, k ∈ Finset.Icc (i + 1) j -> 0 <= turn k) :
    (Finset.Icc a b).sum turn <= separatedTurn turn i j :=
  turnSubwindow_sum_le_separatedTurn
    (Finset.Icc_subset_Icc ha hb) hnonneg

/-- Global nonnegativity form of the interval-subwindow comparison. -/
theorem turnSubwindowIcc_sum_le_separatedTurn_of_nonneg
    {turn : Nat -> Real} {i j a b : Nat}
    (ha : i + 1 <= a) (hb : b <= j)
    (hnonneg : forall k : Nat, 0 <= turn k) :
    (Finset.Icc a b).sum turn <= separatedTurn turn i j :=
  turnSubwindowIcc_sum_le_separatedTurn ha hb
    (fun k _hk => hnonneg k)

/-- A bound by the whole separated interval is already the separated-turn
containment. -/
theorem central_angle_le_separatedTurn_of_turnWindowSum
    {turn : Nat -> Real} {i j : Nat} {p qi qj : Point}
    (hangle : angleAt qi p qj <= (Finset.Icc (i + 1) j).sum turn) :
    angleAt qi p qj <= separatedTurn turn i j := by
  simpa [separatedTurn] using hangle

/-- If the central angle is bounded by a turn subwindow of the separated
interval, local turn nonnegativity proves the actual Figure 8 S5
inequality. -/
theorem central_angle_le_separatedTurn_of_turnSubwindow_on_window
    {turn : Nat -> Real} {i j : Nat} {p qi qj : Point}
    (hnonneg :
      forall k : Nat, k ∈ Finset.Icc (i + 1) j -> 0 <= turn k)
    (H : CentralAngleTurnSubwindow turn i j p qi qj) :
    angleAt qi p qj <= separatedTurn turn i j := by
  rcases H with ⟨window, hsub, hangle⟩
  refine le_trans hangle ?_
  exact turnSubwindow_sum_le_separatedTurn hsub hnonneg

/-- If the central angle is bounded by a turn subwindow of the separated
interval, pointwise turn nonnegativity proves the actual Figure 8 S5
inequality. -/
theorem central_angle_le_separatedTurn_of_turnSubwindow
    {turn : Nat -> Real} {i j : Nat} {p qi qj : Point}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : CentralAngleTurnSubwindow turn i j p qi qj) :
    angleAt qi p qj <= separatedTurn turn i j :=
  central_angle_le_separatedTurn_of_turnSubwindow_on_window
    (fun k _hk => hnonneg k) H

/-- Exact subwindow data is a special case of subwindow inequality data. -/
theorem turnSubwindow_of_turnSubwindowEq
    {turn : Nat -> Real} {i j : Nat} {p qi qj : Point}
    (H : CentralAngleTurnSubwindowEq turn i j p qi qj) :
    CentralAngleTurnSubwindow turn i j p qi qj := by
  rcases H with ⟨window, hsub, hangle⟩
  exact ⟨window, hsub, le_of_eq hangle⟩

/-- Exact telescope form of the previous reduction: if the central angle is
equal to a turn subwindow sum, nonnegativity embeds it into the separated turn
window. -/
theorem central_angle_le_separatedTurn_of_turnSubwindow_eq
    {turn : Nat -> Real} {i j : Nat} {p qi qj : Point}
    (hnonneg : forall k : Nat, 0 <= turn k)
    {window : Finset Nat}
    (hsub : window <= Finset.Icc (i + 1) j)
    (hangle : angleAt qi p qj = window.sum turn) :
    angleAt qi p qj <= separatedTurn turn i j :=
  central_angle_le_separatedTurn_of_turnSubwindow hnonneg
    ⟨window, hsub, le_of_eq hangle⟩

/-- Interval-subwindow form: a central-angle bound by any interval inside the
separated turn window proves the separated-turn containment. -/
theorem central_angle_le_separatedTurn_of_turnSubwindowIcc
    {turn : Nat -> Real} {i j a b : Nat} {p qi qj : Point}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (ha : i + 1 <= a) (hb : b <= j)
    (hangle : angleAt qi p qj <= (Finset.Icc a b).sum turn) :
    angleAt qi p qj <= separatedTurn turn i j := by
  exact le_trans hangle
    (turnSubwindowIcc_sum_le_separatedTurn_of_nonneg ha hb hnonneg)

/-- Exact interval telescope form of the previous lemma. -/
theorem central_angle_le_separatedTurn_of_turnSubwindowIcc_eq
    {turn : Nat -> Real} {i j a b : Nat} {p qi qj : Point}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (ha : i + 1 <= a) (hb : b <= j)
    (hangle : angleAt qi p qj = (Finset.Icc a b).sum turn) :
    angleAt qi p qj <= separatedTurn turn i j :=
  central_angle_le_separatedTurn_of_turnSubwindowIcc
    hnonneg ha hb (le_of_eq hangle)

/-- Interval-subwindow data produces the generic finite subwindow source. -/
theorem turnSubwindow_of_turnSubwindowIcc
    {turn : Nat -> Real} {i j a b : Nat} {p qi qj : Point}
    (ha : i + 1 <= a) (hb : b <= j)
    (hangle : angleAt qi p qj <= (Finset.Icc a b).sum turn) :
    CentralAngleTurnSubwindow turn i j p qi qj :=
  ⟨Finset.Icc a b, Finset.Icc_subset_Icc ha hb, hangle⟩

/-- Exact interval-subwindow data produces the generic exact subwindow source. -/
theorem turnSubwindowEq_of_turnSubwindowIcc_eq
    {turn : Nat -> Real} {i j a b : Nat} {p qi qj : Point}
    (ha : i + 1 <= a) (hb : b <= j)
    (hangle : angleAt qi p qj = (Finset.Icc a b).sum turn) :
    CentralAngleTurnSubwindowEq turn i j p qi qj :=
  ⟨Finset.Icc a b, Finset.Icc_subset_Icc ha hb, hangle⟩

/-- Indexed finite telescope source: the angle is bounded by turns at an
injectively indexed finite list of slots, all lying in the separated
subwindow. -/
def CentralAngleTurnIndexedSubwindow
    (turn : Nat -> Real) (i j : Nat) (p qi qj : Point) : Prop :=
  Exists fun m : Nat =>
  Exists fun index : Fin m -> Nat =>
    Function.Injective index /\
      (forall t : Fin m, index t ∈ Finset.Icc (i + 1) j) /\
        angleAt qi p qj <= Finset.univ.sum (fun t : Fin m => turn (index t))

/-- Exact indexed finite telescope source. -/
def CentralAngleTurnIndexedSubwindowEq
    (turn : Nat -> Real) (i j : Nat) (p qi qj : Point) : Prop :=
  Exists fun m : Nat =>
  Exists fun index : Fin m -> Nat =>
    Function.Injective index /\
      (forall t : Fin m, index t ∈ Finset.Icc (i + 1) j) /\
        angleAt qi p qj = Finset.univ.sum (fun t : Fin m => turn (index t))

/-- An indexed finite telescope is an ordinary turn subwindow, by taking the
image of the finite index map. -/
theorem turnSubwindow_of_indexedSubwindow
    {turn : Nat -> Real} {i j : Nat} {p qi qj : Point}
    (H : CentralAngleTurnIndexedSubwindow turn i j p qi qj) :
    CentralAngleTurnSubwindow turn i j p qi qj := by
  rcases H with ⟨m, index, hinj, hmem, hangle⟩
  refine ⟨Finset.univ.image index, ?_, ?_⟩
  · intro k hk
    rcases Finset.mem_image.mp hk with ⟨t, _ht, rfl⟩
    exact hmem t
  · have hsum_image :
        (Finset.univ.image index).sum turn =
          Finset.univ.sum (fun t : Fin m => turn (index t)) := by
      rw [Finset.sum_image]
      intro x _hx y _hy hxy
      exact hinj hxy
    simpa [hsum_image] using hangle

/-- An exact indexed finite telescope is an ordinary exact turn subwindow. -/
theorem turnSubwindowEq_of_indexedSubwindowEq
    {turn : Nat -> Real} {i j : Nat} {p qi qj : Point}
    (H : CentralAngleTurnIndexedSubwindowEq turn i j p qi qj) :
    CentralAngleTurnSubwindowEq turn i j p qi qj := by
  rcases H with ⟨m, index, hinj, hmem, hangle⟩
  refine ⟨Finset.univ.image index, ?_, ?_⟩
  · intro k hk
    rcases Finset.mem_image.mp hk with ⟨t, _ht, rfl⟩
    exact hmem t
  · have hsum_image :
        (Finset.univ.image index).sum turn =
          Finset.univ.sum (fun t : Fin m => turn (index t)) := by
      rw [Finset.sum_image]
      intro x _hx y _hy hxy
      exact hinj hxy
    rw [hsum_image]
    exact hangle

/-- Row-wise subwindow source for the remaining Figure 8 angle containment
obligation.  It quantifies over the same admissible distance data as the
existing central-angle containment row, but asks for a checkable turn-subwindow
bound instead of the final `separatedTurn` conclusion. -/
def Figure8CentralAngleTurnSubwindowRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i j : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
    Figure8DistanceData p qi qj s r ->
      CentralAngleTurnSubwindow turn i j p qi qj

/-- Row-wise exact telescope source for the remaining Figure 8 angle
containment obligation. -/
def Figure8CentralAngleTurnSubwindowEqRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i j : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
    Figure8DistanceData p qi qj s r ->
      CentralAngleTurnSubwindowEq turn i j p qi qj

/-- Row-wise interval-subwindow source for Figure 8.  This is stronger than
the arbitrary finite-subwindow source and matches a consecutive turn
telescope. -/
def Figure8CentralAngleTurnIccSubwindowRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i j : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
    Figure8DistanceData p qi qj s r ->
      Exists fun a : Nat =>
      Exists fun b : Nat =>
        i + 1 <= a /\
          b <= j /\
            angleAt qi p qj <= (Finset.Icc a b).sum turn

/-- Row-wise exact interval telescope source for Figure 8. -/
def Figure8CentralAngleTurnIccSubwindowEqRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i j : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
    Figure8DistanceData p qi qj s r ->
      Exists fun a : Nat =>
      Exists fun b : Nat =>
        i + 1 <= a /\
          b <= j /\
            angleAt qi p qj = (Finset.Icc a b).sum turn

/-- Row-wise indexed finite telescope source for Figure 8. -/
def Figure8CentralAngleTurnIndexedSubwindowRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i j : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
    Figure8DistanceData p qi qj s r ->
      CentralAngleTurnIndexedSubwindow turn i j p qi qj

/-- Row-wise exact indexed finite telescope source for Figure 8. -/
def Figure8CentralAngleTurnIndexedSubwindowEqRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i j : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
    Figure8DistanceData p qi qj s r ->
      CentralAngleTurnIndexedSubwindowEq turn i j p qi qj

/-- Exact subwindow rows are a special case of subwindow inequality rows. -/
theorem turnSubwindowRows_of_turnSubwindowEqRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8CentralAngleTurnSubwindowEqRows good turn) :
    Figure8CentralAngleTurnSubwindowRows good turn := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
  exact turnSubwindow_of_turnSubwindowEq
    (H hi hsep hj hbad_i hbad_j D)

/-- Interval-subwindow rows are a special case of finite subwindow rows. -/
theorem turnSubwindowRows_of_turnSubwindowIccRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8CentralAngleTurnIccSubwindowRows good turn) :
    Figure8CentralAngleTurnSubwindowRows good turn := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
  rcases H hi hsep hj hbad_i hbad_j D with
    ⟨a, b, ha, hb, hangle⟩
  exact turnSubwindow_of_turnSubwindowIcc ha hb hangle

/-- Exact interval-telescope rows are a special case of exact finite
subwindow rows. -/
theorem turnSubwindowEqRows_of_turnSubwindowIccEqRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8CentralAngleTurnIccSubwindowEqRows good turn) :
    Figure8CentralAngleTurnSubwindowEqRows good turn := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
  rcases H hi hsep hj hbad_i hbad_j D with
    ⟨a, b, ha, hb, hangle⟩
  exact turnSubwindowEq_of_turnSubwindowIcc_eq ha hb hangle

/-- Indexed finite telescope rows are a special case of finite subwindow
rows. -/
theorem turnSubwindowRows_of_indexedSubwindowRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8CentralAngleTurnIndexedSubwindowRows good turn) :
    Figure8CentralAngleTurnSubwindowRows good turn := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
  exact turnSubwindow_of_indexedSubwindow
    (H hi hsep hj hbad_i hbad_j D)

/-- Exact indexed finite telescope rows are a special case of exact finite
subwindow rows. -/
theorem turnSubwindowEqRows_of_indexedSubwindowEqRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8CentralAngleTurnIndexedSubwindowEqRows good turn) :
    Figure8CentralAngleTurnSubwindowEqRows good turn := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
  exact turnSubwindowEq_of_indexedSubwindowEq
    (H hi hsep hj hbad_i hbad_j D)

/-- Subwindow rows plus pointwise turn nonnegativity prove the existing
Figure 8 central-angle containment row consumed by S5. -/
theorem centralAngleContainmentRows_of_turnSubwindowRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnSubwindowRows good turn) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      good turn := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
  exact central_angle_le_separatedTurn_of_turnSubwindow hnonneg
    (H hi hsep hj hbad_i hbad_j D)

/-- Local separated-window nonnegativity is enough to turn subwindow rows
into the Figure 8 central-angle containment row. -/
theorem centralAngleContainmentRows_of_turnSubwindowRows_on_windows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg :
      forall {i j k : Nat}, 1 <= i -> i + 1 < j -> j <= 10 ->
        k ∈ Finset.Icc (i + 1) j -> 0 <= turn k)
    (H : Figure8CentralAngleTurnSubwindowRows good turn) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      good turn := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
  exact central_angle_le_separatedTurn_of_turnSubwindow_on_window
    (fun k hk => hnonneg hi hsep hj hk)
    (H hi hsep hj hbad_i hbad_j D)

/-- Exact subwindow/telescope rows plus pointwise turn nonnegativity prove the
existing Figure 8 central-angle containment row consumed by S5. -/
theorem centralAngleContainmentRows_of_turnSubwindowEqRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnSubwindowEqRows good turn) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      good turn :=
  centralAngleContainmentRows_of_turnSubwindowRows hnonneg
    (turnSubwindowRows_of_turnSubwindowEqRows H)

/-- Interval-subwindow rows plus pointwise turn nonnegativity prove the
existing Figure 8 central-angle containment row consumed by S5. -/
theorem centralAngleContainmentRows_of_turnSubwindowIccRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnIccSubwindowRows good turn) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      good turn :=
  centralAngleContainmentRows_of_turnSubwindowRows hnonneg
    (turnSubwindowRows_of_turnSubwindowIccRows H)

/-- Exact interval-telescope rows plus pointwise turn nonnegativity prove the
existing Figure 8 central-angle containment row consumed by S5. -/
theorem centralAngleContainmentRows_of_turnSubwindowIccEqRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnIccSubwindowEqRows good turn) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      good turn :=
  centralAngleContainmentRows_of_turnSubwindowEqRows hnonneg
    (turnSubwindowEqRows_of_turnSubwindowIccEqRows H)

/-- Indexed finite telescope rows plus pointwise turn nonnegativity prove the
existing Figure 8 central-angle containment row consumed by S5. -/
theorem centralAngleContainmentRows_of_indexedSubwindowRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnIndexedSubwindowRows good turn) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      good turn :=
  centralAngleContainmentRows_of_turnSubwindowRows hnonneg
    (turnSubwindowRows_of_indexedSubwindowRows H)

/-- Exact indexed finite telescope rows plus pointwise turn nonnegativity
prove the existing Figure 8 central-angle containment row consumed by S5. -/
theorem centralAngleContainmentRows_of_indexedSubwindowEqRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnIndexedSubwindowEqRows good turn) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      good turn :=
  centralAngleContainmentRows_of_turnSubwindowEqRows hnonneg
    (turnSubwindowEqRows_of_indexedSubwindowEqRows H)

/-- M8 turn bounds provide the nonnegativity needed by the subwindow rows. -/
theorem centralAngleContainmentRows_of_m8TurnBounds_turnSubwindowRows
    {good : Nat -> Prop} (turnBounds : M8TurnBounds)
    (H :
      Figure8CentralAngleTurnSubwindowRows good turnBounds.turn) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      good turnBounds.turn :=
  centralAngleContainmentRows_of_turnSubwindowRows
    turnBounds.turn_nonnegative H

/-- M8 turn bounds provide the nonnegativity needed by exact subwindow rows. -/
theorem centralAngleContainmentRows_of_m8TurnBounds_turnSubwindowEqRows
    {good : Nat -> Prop} (turnBounds : M8TurnBounds)
    (H :
      Figure8CentralAngleTurnSubwindowEqRows good turnBounds.turn) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      good turnBounds.turn :=
  centralAngleContainmentRows_of_turnSubwindowEqRows
    turnBounds.turn_nonnegative H

/-- Distance rows plus turn-subwindow rows rebuild the concrete Figure 8
containment interface used by the S5 assembly layers. -/
def containmentInterface_of_distanceWitnessRowsAndTurnSubwindowRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (distanceRows :
      Figure8ContainmentConcrete.Figure8SeparatedDistanceWitnessRows good)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnSubwindowRows good turn) :
    Figure8SeparatedContainmentInterface good turn :=
  Figure8ContainmentConcrete.containmentInterface_of_distanceWitnessRowsAndCentralAngleContainment
    distanceRows
    (centralAngleContainmentRows_of_turnSubwindowRows hnonneg H)

/-- Distance rows plus exact turn-subwindow rows rebuild the concrete Figure 8
containment interface used by the S5 assembly layers. -/
def containmentInterface_of_distanceWitnessRowsAndTurnSubwindowEqRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (distanceRows :
      Figure8ContainmentConcrete.Figure8SeparatedDistanceWitnessRows good)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnSubwindowEqRows good turn) :
    Figure8SeparatedContainmentInterface good turn :=
  containmentInterface_of_distanceWitnessRowsAndTurnSubwindowRows
    distanceRows hnonneg
    (turnSubwindowRows_of_turnSubwindowEqRows H)

/-- Distance rows plus turn-subwindow rows rebuild the explicit Figure 8
Euclidean fact package consumed by W32/W34. -/
def explicitEuclideanFacts_of_distanceWitnessRowsAndTurnSubwindowRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (distanceRows :
      Figure8ContainmentConcrete.Figure8SeparatedDistanceWitnessRows good)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnSubwindowRows good turn) :
    Figure8ExplicitEuclideanFacts good turn :=
  Figure8ExplicitEuclideanFacts.ofContainmentInterface
    (containmentInterface_of_distanceWitnessRowsAndTurnSubwindowRows
      distanceRows hnonneg H)

/-- Distance rows plus exact turn-subwindow rows rebuild the explicit Figure 8
Euclidean fact package consumed by W32/W34. -/
def explicitEuclideanFacts_of_distanceWitnessRowsAndTurnSubwindowEqRows
    {good : Nat -> Prop} {turn : Nat -> Real}
    (distanceRows :
      Figure8ContainmentConcrete.Figure8SeparatedDistanceWitnessRows good)
    (hnonneg : forall k : Nat, 0 <= turn k)
    (H : Figure8CentralAngleTurnSubwindowEqRows good turn) :
    Figure8ExplicitEuclideanFacts good turn :=
  explicitEuclideanFacts_of_distanceWitnessRowsAndTurnSubwindowRows
    distanceRows hnonneg
    (turnSubwindowRows_of_turnSubwindowEqRows H)

/-- Prop-level selected Figure 8 distance data together with the central-angle
containment that places the selected angle inside the separated turn window.

The package is intentionally `Prop`: `Figure8ExplicitEuclideanFacts` is also a
`Prop`, so this is the strongest honest selected package that can be projected
from it without using choice. -/
def SelectedDistanceContainment
    (turn : Nat -> Real) (i j : Nat) : Prop :=
  Exists fun p : Point =>
  Exists fun qi : Point =>
  Exists fun qj : Point =>
  Exists fun s : Point =>
  Exists fun r : Point =>
    Figure8DistanceData p qi qj s r /\
      angleAt qi p qj <= separatedTurn turn i j

namespace SelectedDistanceContainment

variable {turn : Nat -> Real} {i j : Nat}

/-- The selected distance package carries the checked central-angle lower
bound. -/
theorem central_angle_lower
    (D : SelectedDistanceContainment turn i j) :
    Exists fun p : Point =>
    Exists fun qi : Point =>
    Exists fun qj : Point =>
      Real.pi / 3 <= angleAt qi p qj := by
  rcases D with ⟨p, qi, qj, _s, _r, Ddist, _hcontained⟩
  exact
    ⟨p, qi, qj,
      _root_.ErdosProblems1066.Swanepoel.Figure8EuclideanFactsConcrete.central_angle_lower
        Ddist⟩

/-- The selected distance package and its containment proof give the local
separated-turn lower bound. -/
theorem separatedTurn_lower
    (D : SelectedDistanceContainment turn i j) :
    Real.pi / 3 <= separatedTurn turn i j := by
  rcases D with ⟨_p, _qi, _qj, _s, _r, Ddist, hcontained⟩
  exact le_trans
    (_root_.ErdosProblems1066.Swanepoel.Figure8EuclideanFactsConcrete.central_angle_lower
      Ddist)
    hcontained

end SelectedDistanceContainment

/-- Select the Figure 8 distance/containment package determined by explicit
Euclidean facts at a separated failed pair. -/
theorem selectedDistanceContainment
    (H : Figure8ExplicitEuclideanFacts good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    SelectedDistanceContainment turn i j := by
  rcases H.distance_data hi hsep hj hbad_i hbad_j with
    ⟨p, qi, qj, s, r, D⟩
  exact
    ⟨p, qi, qj, s, r, D,
      H.central_angle_le_separatedTurn hi hsep hj hbad_i hbad_j D⟩

/-- Direct E22 projection from the selected Figure 8 distance data and
central-angle containment. -/
theorem E22_via_selectedEuclideanFacts
    (H : Figure8ExplicitEuclideanFacts good turn) :
    Figure8SeparatedWindowLowerE22 good turn := by
  intro i j hi hsep hj hbad_i hbad_j
  exact
    (H.selectedDistanceContainment hi hsep hj hbad_i hbad_j).separatedTurn_lower

/-- Pointwise form of the direct selected-witness E22 projection. -/
theorem E22_apply_via_selectedEuclideanFacts
    (H : Figure8ExplicitEuclideanFacts good turn)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Real.pi / 3 <= separatedTurn turn i j :=
  H.E22_via_selectedEuclideanFacts hi hsep hj hbad_i hbad_j

/-- Concrete containment interfaces imply E22 through selected Figure 8
Euclidean facts. -/
theorem E22_of_containmentInterface_via_selectedEuclideanFacts
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  (ofContainmentInterface H).E22_via_selectedEuclideanFacts

end Figure8ExplicitEuclideanFacts

/-! ## Honest M8 projections -/

/-- Explicit honest Figure 8 facts give the honest E22 hypothesis through
selected Euclidean facts. -/
theorem honestFigure8SeparatedWindowLowerE22_of_explicitEuclideanFacts_via_selectedEuclideanFacts
    {V : Type u} {G : LocalGraph V}
    {P : M8HonestLocalPredicates G} {turn : Nat -> Real}
    (H : HonestFigure8ExplicitEuclideanFacts P turn) :
    HonestFigure8SeparatedWindowLowerE22 P turn :=
  H.E22_via_selectedEuclideanFacts

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- The Figure 8 field of an M8 window-containment package as selected
Euclidean fact witnesses. -/
def honestSelectedEuclideanFactWitnesses_of_m8WindowContainment
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn :=
  euclideanFactWitnesses_of_containmentInterface W.figure8

/-- Projection to honest E22 from an M8 window-containment package through
the selected Figure 8 Euclidean fact route. -/
theorem honestFigure8SeparatedWindowLowerE22_of_m8WindowContainment_via_selectedEuclideanFacts
    (W : M8WindowContainment localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  (honestExplicitEuclideanFacts_of_m8WindowContainment W).E22_via_selectedEuclideanFacts

end Figure8EuclideanFactsConcrete
end Swanepoel
end ErdosProblems1066

end
