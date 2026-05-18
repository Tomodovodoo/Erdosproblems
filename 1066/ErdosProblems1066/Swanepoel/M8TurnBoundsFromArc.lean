import ErdosProblems1066.Swanepoel.M8ConstructionInterface
import ErdosProblems1066.Swanepoel.TurnBoundsInterface

/-!
# M8 turn bounds from a nonconcave arc

This file is a conditional bridge from the explicit long nonconcave-arc turn
data into the two checked turn-bound interfaces used downstream.

The supplied arc data is intentionally small: a raw turn function, pointwise
nonnegativity on the `m = 8` arc indices `1, ..., 13`, and the nonconcavity
bound on the same total turn.  The bridge normalizes the turn function by
zeroing it off the arc, so it satisfies the global nonnegativity field required
by `TurnBoundsInterface.HonestTurnBounds` without adding any geometric content.

The optional containment packages below keep the Figure 8/Figure 9 geometry
explicit.  They route selected distance data and angle containment through the
existing `Lemma10AngleToTurn` and `Lemma10Inequalities` pipeline.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace M8TurnBoundsFromArc

open AngleContainmentInterface
open GraphBridge
open Lemma10AnalyticBridge
open Lemma10AngleToTurn
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open LocalConfigurations
open M8ConstructionInterface
open MinimalGraphFacts
open TurnBoundsInterface

universe u

/-! ## Turn-bound conversions -/

/-- Forget the `M8ConstructionInterface` turn-bound record to the generic
honest turn-bound package. -/
def honestTurnBounds_of_m8TurnBounds
    (T : M8ConstructionInterface.M8TurnBounds) :
    TurnBoundsInterface.HonestTurnBounds where
  turn := T.turn
  turn_nonnegative := T.turn_nonnegative
  total_turn_lt_pi_div_three := T.total_turn_lt_pi_div_three

/-- Package an honest turn-bound record as the turn-bound field expected by
`M8ConstructionInterface`. -/
def m8TurnBounds_of_honestTurnBounds
    (T : TurnBoundsInterface.HonestTurnBounds) :
    M8ConstructionInterface.M8TurnBounds where
  turn := T.turn
  turn_nonnegative := T.turn_nonnegative
  total_turn_lt_pi_div_three := T.total_turn_lt_pi_div_three

@[simp] theorem honestTurnBounds_of_m8TurnBounds_turn
    (T : M8ConstructionInterface.M8TurnBounds) :
    (honestTurnBounds_of_m8TurnBounds T).turn = T.turn :=
  rfl

@[simp] theorem m8TurnBounds_of_honestTurnBounds_turn
    (T : TurnBoundsInterface.HonestTurnBounds) :
    (m8TurnBounds_of_honestTurnBounds T).turn = T.turn :=
  rfl

/-! ## Explicit nonconcave arc turn data -/

/-- Explicit turn data supplied by a nonconcave `m = 8` arc.

Only the indices in `turnIndexSet = {1, ..., 13}` are part of the arc.  The
bridge below clamps the raw turn function to zero off this set before producing
the global honest turn package. -/
structure NonconcaveArcTurnData where
  rawTurn : Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall k : Nat, k ∈ turnIndexSet -> 0 <= rawTurn k
  raw_totalTurn_lt_pi_div_three :
    totalTurn rawTurn < Real.pi / 3

namespace NonconcaveArcTurnData

/-- The normalized turn function: the supplied arc turns on `1, ..., 13`, and
zero outside that range. -/
def turn (A : NonconcaveArcTurnData) (k : Nat) : Real :=
  if k ∈ turnIndexSet then A.rawTurn k else 0

@[simp] theorem turn_of_mem (A : NonconcaveArcTurnData) {k : Nat}
    (hk : k ∈ turnIndexSet) :
    A.turn k = A.rawTurn k := by
  simp [turn, hk]

@[simp] theorem turn_of_not_mem (A : NonconcaveArcTurnData) {k : Nat}
    (hk : k ∉ turnIndexSet) :
    A.turn k = 0 := by
  simp [turn, hk]

/-- The normalized turn function is nonnegative at every natural index. -/
theorem turn_nonnegative (A : NonconcaveArcTurnData) (k : Nat) :
    0 <= A.turn k := by
  by_cases hk : k ∈ turnIndexSet
  case pos =>
    simpa [turn, hk] using A.rawTurn_nonnegative_on_arc k hk
  case neg =>
    simp [turn, hk]

/-- Normalizing off-arc indices does not change the total turn used by Lemma
10, since that total only sums over `turnIndexSet`. -/
theorem totalTurn_turn_eq_rawTurn (A : NonconcaveArcTurnData) :
    totalTurn A.turn = totalTurn A.rawTurn := by
  unfold totalTurn
  apply Finset.sum_congr rfl
  intro k hk
  exact A.turn_of_mem hk

/-- The normalized arc turn data as an honest turn-bound package. -/
def toHonestTurnBounds (A : NonconcaveArcTurnData) :
    TurnBoundsInterface.HonestTurnBounds where
  turn := A.turn
  turn_nonnegative := A.turn_nonnegative
  total_turn_lt_pi_div_three := by
    simpa [A.totalTurn_turn_eq_rawTurn] using
      A.raw_totalTurn_lt_pi_div_three

/-- The normalized arc turn data as the turn-bound field expected by
`M8ConstructionInterface`. -/
def toM8TurnBounds (A : NonconcaveArcTurnData) :
    M8ConstructionInterface.M8TurnBounds :=
  m8TurnBounds_of_honestTurnBounds A.toHonestTurnBounds

@[simp] theorem toHonestTurnBounds_turn (A : NonconcaveArcTurnData) :
    A.toHonestTurnBounds.turn = A.turn :=
  rfl

@[simp] theorem toM8TurnBounds_turn (A : NonconcaveArcTurnData) :
    A.toM8TurnBounds.turn = A.turn :=
  rfl

/-- The nonconcave arc's total-turn bound after normalization. -/
theorem totalTurn_turn_lt_pi_div_three (A : NonconcaveArcTurnData) :
    totalTurn A.turn < Real.pi / 3 :=
  A.toHonestTurnBounds.total_turn_lt_pi_div_three

/-- Any separated turn window inherits nonnegativity from the normalized
honest turn package. -/
theorem separatedTurn_nonnegative (A : NonconcaveArcTurnData)
    (i j : Nat) :
    0 <= separatedTurn A.turn i j :=
  A.toHonestTurnBounds.separatedTurn_nonnegative i j

/-- Any adjacent turn window inherits nonnegativity from the normalized honest
turn package. -/
theorem adjacentTurn_nonnegative (A : NonconcaveArcTurnData)
    (i : Nat) :
    0 <= adjacentTurn A.turn i :=
  A.toHonestTurnBounds.adjacentTurn_nonnegative i

end NonconcaveArcTurnData

/-! ## Explicit containment geometry to window geometry -/

/-- A selected Figure 8 containment interface is also the explicit window
geometry interface used by `M8ConstructionInterface`. -/
def figure8SeparatedWindowGeometry_of_containment
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure8SeparatedContainmentInterface good turn) :
    Figure8SeparatedWindowGeometry good turn := by
  intro i j hi hsep hj hbad_i hbad_j
  let D := H.extractedData hi hsep hj hbad_i hbad_j
  exact Exists.intro D.p <|
    Exists.intro D.qi <|
      Exists.intro D.qj <|
        Exists.intro D.s <|
          Exists.intro D.r <|
            And.intro D.distanceData
              (H.central_angle_le_separatedTurn hi hsep hj hbad_i hbad_j
                D.distanceData)

/-- A selected Figure 9 left-angle containment interface is also the explicit
window geometry interface used by `M8ConstructionInterface`. -/
def figure9AdjacentLeftWindowGeometry_of_containment
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9AdjacentLeftWindowGeometry good turn := by
  intro i hi hi_next hbad_i hbad_next
  let D := H.extractedData hi hi_next hbad_i hbad_next
  exact Exists.intro D.p <|
    Exists.intro D.qi <|
      Exists.intro D.qj <|
        Exists.intro D.s <|
          Exists.intro D.r <|
            And.intro D.distanceData
              (H.left_angle_le_adjacentTurn hi hi_next hbad_i hbad_next
                D.distanceData)

/-! ## Arc data plus explicit angle-to-turn geometry -/

/-- Nonconcave arc turn data together with the explicit Figure 8/Figure 9
angle-to-turn bridge records for one honest local `m = 8` package. -/
structure M8ArcAngleData {V : Type u} {G : LocalGraph V}
    (P : M8HonestLocalPredicates G) where
  arc : NonconcaveArcTurnData
  figure8 :
    Figure8SeparatedAngleToTurnBridge
      (M8BrokenLatticeGood P.data) arc.turn
  figure9 :
    Figure9AdjacentLeftAngleToTurnBridge
      (M8BrokenLatticeGood P.data) arc.turn

namespace M8ArcAngleData

variable {V : Type u} {G : LocalGraph V}
variable {P : M8HonestLocalPredicates G}

/-- Route explicit nonconcave arc data and angle-to-turn geometry to the
honest turn package used by `TurnBoundsInterface`. -/
def toM8HonestTurnPackage (D : M8ArcAngleData P) :
    TurnBoundsInterface.M8HonestTurnPackage P :=
  TurnBoundsInterface.M8HonestTurnPackage.ofAngleToTurnBridges
    D.arc.toHonestTurnBounds D.figure8 D.figure9

/-- The existing angle-to-turn bridge yields the named E22/E23 hypotheses. -/
theorem E22_E23 (D : M8ArcAngleData P) :
    HonestFigure8SeparatedWindowLowerE22 P D.arc.turn /\
      HonestFigure9AdjacentWindowLowerE23 P D.arc.turn :=
  D.toM8HonestTurnPackage.E22_E23

/-- The explicit arc/geometry package gives the Lemma 10 at-most-one-failure
conclusion. -/
theorem atMostOneFailure (D : M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    P.AtMostOneFailure :=
  D.toM8HonestTurnPackage.atMostOneFailure

end M8ArcAngleData

/-! ## Arc data plus explicit containment geometry for construction fields -/

/-- Nonconcave arc turn data together with selected Figure 8/Figure 9 data and
angle containment, tied to the local labels used by `M8ConstructionInterface`.
-/
structure M8ArcContainmentData {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C) where
  arc : NonconcaveArcTurnData
  containment :
    AngleContainmentBridges
      (M8BrokenLatticeGood localLabels.predicates.data) arc.turn

namespace M8ArcContainmentData

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8ConstructionInterface.M8LocalLabels C}

/-- Forget selected containment witnesses to the angle-to-turn bridge records.
-/
def toM8ArcAngleData (D : M8ArcContainmentData localLabels) :
    M8ArcAngleData localLabels.predicates where
  arc := D.arc
  figure8 := D.containment.figure8.toAngleToTurnBridge
  figure9 := D.containment.figure9.toAngleToTurnBridge

/-- Route explicit containment data through `TurnBoundsInterface`. -/
def toM8HonestTurnPackage (D : M8ArcContainmentData localLabels) :
    TurnBoundsInterface.M8HonestTurnPackage localLabels.predicates :=
  D.toM8ArcAngleData.toM8HonestTurnPackage

/-- Convert explicit containment data to the window-geometry field expected by
`M8ConstructionInterface`. -/
def toM8WindowGeometry (D : M8ArcContainmentData localLabels) :
    M8ConstructionInterface.M8WindowGeometry
      localLabels D.arc.toM8TurnBounds where
  figure8 :=
    figure8SeparatedWindowGeometry_of_containment D.containment.figure8
  figure9_left :=
    figure9AdjacentLeftWindowGeometry_of_containment D.containment.figure9

/-- Assemble the `M8ConstructionInterface` package once the label-level
late-triples field is supplied. -/
def toM8ConstructionData
    {hmin : IsMinimalClearedFailure C}
    (D : M8ArcContainmentData localLabels)
    (lateTriples : M8ConstructionInterface.M8LateTriples localLabels) :
    M8ConstructionInterface.M8ConstructionData C hmin where
  localLabels := localLabels
  turnBounds := D.arc.toM8TurnBounds
  lateTriples := lateTriples
  windowGeometry := D.toM8WindowGeometry

/-- The same assembled construction package, forgotten to the existing
broken-lattice minimal-failure interface. -/
def toBrokenLatticeConstructionData
    {hmin : IsMinimalClearedFailure C}
    (D : M8ArcContainmentData localLabels)
    (lateTriples : M8ConstructionInterface.M8LateTriples localLabels) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  (D.toM8ConstructionData lateTriples).toBrokenLatticeMinimalFailure

end M8ArcContainmentData

end M8TurnBoundsFromArc
end Swanepoel
end ErdosProblems1066

end
