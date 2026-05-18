import ErdosProblems1066.PachToth.ClosedChainConstruction

/-!
# Algebraic consequences of closed-placement transition data

This module extracts reusable finite/transition facts from the existing
Pach--Toth closed-placement interfaces.  It does not construct any new
closed placement: all results are consequences of already supplied point maps
and one-step transition certificates.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementAlgebra

open Arithmetic
open FiniteGraph
open ClosedPlacementInterface

noncomputable section

abbrev R2 := Prod Real Real

/-- The one-step target equation carried by an explicit transition closed
placement certificate. -/
theorem transition_target_eq_placeNext
    {k : Nat} {hk : 0 < k}
    (C : ExplicitTransitionClosedPlacementCertificate k hk)
    (i : Fin k) (v : LocalVertex) :
    C.point (cyclicSucc hk i) v =
      (C.transition i).transition.placeNext (C.point i) v :=
  (C.transition i).target_eq_placeNext v

/-- The one-step target equation for certificates built from same/opposite
transition obligations is exactly the supplied successor equation. -/
theorem sameOpposite_transition_target_eq_placeNext
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (target_eq_placeNext :
      forall i : Fin k, forall v : LocalVertex,
        point (cyclicSucc hk i) v =
          (O.transitionFor (orientation i)).placeNext (point i) v)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1)
    (i : Fin k) (v : LocalVertex) :
    (ClosedChainConstruction.explicitTransitionCertificateOfSameOpposite
        O point orientation target_eq_placeNext separated same_block_edges_unit
      |>.transition i).target_eq_placeNext v =
      target_eq_placeNext i v :=
  rfl

/-- Certificates built from same/opposite obligations retain the supplied
orientation word on each successor transition. -/
theorem sameOpposite_transition_orientation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (target_eq_placeNext :
      forall i : Fin k, forall v : LocalVertex,
        point (cyclicSucc hk i) v =
          (O.transitionFor (orientation i)).placeNext (point i) v)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1)
    (i : Fin k) :
    (ClosedChainConstruction.explicitTransitionCertificateOfSameOpposite
        O point orientation target_eq_placeNext separated same_block_edges_unit
      |>.transition i).transition.orientation = orientation i := by
  simp [ClosedChainConstruction.explicitTransitionCertificateOfSameOpposite,
    Figure2Certificate.SameOppositeTransitionObligations.transitionCertificateFor,
    Figure2Certificate.SameOppositeTransitionObligations.transitionFor_orientation]

/-- The block obtained after following the first `n` transitions from `i`,
using the orientation word read along cyclic successors. -/
def iteratedTransitionBlock
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) : Nat -> LocalVertex -> R2
  | 0 => point i
  | n + 1 =>
      (O.transitionFor (orientation ((cyclicSucc hk)^[n] i))).placeNext
        (iteratedTransitionBlock O hk point orientation i n)

@[simp]
theorem iteratedTransitionBlock_zero
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) :
    iteratedTransitionBlock O hk point orientation i 0 = point i :=
  rfl

@[simp]
theorem iteratedTransitionBlock_succ_apply
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (n : Nat) (v : LocalVertex) :
    iteratedTransitionBlock O hk point orientation i (n + 1) v =
      (O.transitionFor (orientation ((cyclicSucc hk)^[n] i))).placeNext
        (iteratedTransitionBlock O hk point orientation i n) v :=
  rfl

/-- Iterating the transition maps agrees with iterating the cyclic successor
on the block index, provided the one-step successor equations are supplied. -/
theorem iteratedTransitionBlock_eq_point_iterate
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (target_eq_placeNext :
      forall i : Fin k, forall v : LocalVertex,
        point (cyclicSucc hk i) v =
          (O.transitionFor (orientation i)).placeNext (point i) v)
    (i : Fin k) (n : Nat) (v : LocalVertex) :
    iteratedTransitionBlock O hk point orientation i n v =
      point ((cyclicSucc hk)^[n] i) v := by
  revert v
  induction n with
  | zero =>
      intro v
      rfl
  | succ n ih =>
      intro v
      rw [iteratedTransitionBlock_succ_apply]
      have hblock :
          iteratedTransitionBlock O hk point orientation i n =
            point ((cyclicSucc hk)^[n] i) := by
        funext w
        exact ih w
      rw [hblock]
      simpa [Function.iterate_succ_apply'] using
        (target_eq_placeNext ((cyclicSucc hk)^[n] i) v).symm

/-- If an iterate of the cyclic successor returns to the starting index, then
the corresponding iterated transition block returns to the starting placed
block. -/
theorem iteratedTransitionBlock_eq_point_of_index_period
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (target_eq_placeNext :
      forall i : Fin k, forall v : LocalVertex,
        point (cyclicSucc hk i) v =
          (O.transitionFor (orientation i)).placeNext (point i) v)
    (i : Fin k) {n : Nat}
    (hperiod : ((cyclicSucc hk)^[n]) i = i)
    (v : LocalVertex) :
    iteratedTransitionBlock O hk point orientation i n v = point i v := by
  rw [iteratedTransitionBlock_eq_point_iterate
    O point orientation target_eq_placeNext]
  rw [hperiod]

end

end ClosedPlacementAlgebra
end PachToth
end ErdosProblems1066
