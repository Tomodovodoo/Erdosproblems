import ErdosProblems1066.PachToth.GeneratedClosedChain
import ErdosProblems1066.PachToth.CyclicIndex

set_option autoImplicit false

/-!
# Generated-chain period interface

This module names the two period/closure equations used by the generated
closed-chain pipeline and proves that, for the generated chain, the final
block equation is the same as closure of the algebraic iterated-transition
block from index `0`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodInterface

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The concrete generated-chain period equation: after `k` generated
transition steps, the block returns to the chosen base block. -/
def GeneratedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  GeneratedClosedChain.generatedBlock O hk base orientation k = base

/-- The same closure requirement, expressed in the iterated-transition
algebra from `ClosedPlacementAlgebra`, starting at cyclic index `0`. -/
def GeneratedClosureEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  ClosedPlacementAlgebra.iteratedTransitionBlock O hk
    (GeneratedClosedChain.generatedPoint O hk base orientation) orientation
    (Fin.mk 0 hk) k = base

/-- Pointwise form of the generated period equation. -/
theorem generatedPeriodEquation_apply
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod : GeneratedPeriodEquation O hk base orientation)
    (v : LocalVertex) :
    GeneratedClosedChain.generatedBlock O hk base orientation k v = base v := by
  exact congrFun hperiod v

/-- Pointwise form of the algebraic generated-closure equation. -/
theorem generatedClosureEquation_apply
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hclosure : GeneratedClosureEquation O hk base orientation)
    (v : LocalVertex) :
    ClosedPlacementAlgebra.iteratedTransitionBlock O hk
      (GeneratedClosedChain.generatedPoint O hk base orientation) orientation
      (Fin.mk 0 hk) k v = base v := by
  exact congrFun hclosure v

/-- For every strictly pre-period block, the generated linear block agrees
with the closed-placement iterated-transition algebra from cyclic index `0`. -/
theorem generatedBlock_eq_iterated_from_zero_of_lt
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    {n : Nat} (hn : n < k) (v : LocalVertex) :
    GeneratedClosedChain.generatedBlock O hk base orientation n v =
      ClosedPlacementAlgebra.iteratedTransitionBlock O hk
        (GeneratedClosedChain.generatedPoint O hk base orientation)
        orientation (Fin.mk 0 hk) n v :=
  GeneratedClosedChain.generatedBlock_eq_closedPlacementAlgebra_iterated_from_zero
    O hk base orientation n hn v

/-- At the final step `k`, the generated block still agrees with the
iterated-transition algebra from cyclic index `0`.  The last pre-period index
is identified by the reusable `CyclicIndex` lemmas. -/
theorem generatedBlock_eq_iterated_from_zero_at_card
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (v : LocalVertex) :
    GeneratedClosedChain.generatedBlock O hk base orientation k v =
      ClosedPlacementAlgebra.iteratedTransitionBlock O hk
        (GeneratedClosedChain.generatedPoint O hk base orientation)
        orientation (Fin.mk 0 hk) k v := by
  have hlast_lt : k - 1 < k := Nat.sub_lt hk Nat.zero_lt_one
  have hlast_index :
      ((cyclicSucc hk)^[k - 1]) (Fin.mk 0 hk : Fin k) =
        Fin.mk (k - 1) hlast_lt :=
    cyclicSucc_iterate_zero_eq_mk_of_lt hk hlast_lt
  have hread :
      GeneratedClosedChain.orientationAt hk orientation (k - 1) =
        orientation (((cyclicSucc hk)^[k - 1]) (Fin.mk 0 hk : Fin k)) := by
    rw [hlast_index]
    exact GeneratedClosedChain.orientationAt_of_lt hk orientation hlast_lt
  have hprev :
      GeneratedClosedChain.generatedBlock O hk base orientation (k - 1) =
        ClosedPlacementAlgebra.iteratedTransitionBlock O hk
          (GeneratedClosedChain.generatedPoint O hk base orientation)
          orientation (Fin.mk 0 hk) (k - 1) := by
    funext w
    exact generatedBlock_eq_iterated_from_zero_of_lt
      O hk base orientation hlast_lt w
  calc
    GeneratedClosedChain.generatedBlock O hk base orientation k v =
        GeneratedClosedChain.generatedBlock O hk base orientation ((k - 1) + 1) v := by
          congr
          omega
    _ =
        (O.transitionFor
          (GeneratedClosedChain.orientationAt hk orientation (k - 1))).placeNext
          (GeneratedClosedChain.generatedBlock O hk base orientation (k - 1)) v := by
          rfl
    _ =
        (O.transitionFor
          (orientation (((cyclicSucc hk)^[k - 1]) (Fin.mk 0 hk : Fin k)))).placeNext
          (ClosedPlacementAlgebra.iteratedTransitionBlock O hk
            (GeneratedClosedChain.generatedPoint O hk base orientation)
            orientation (Fin.mk 0 hk) (k - 1)) v := by
          rw [hread, hprev]
    _ =
        ClosedPlacementAlgebra.iteratedTransitionBlock O hk
          (GeneratedClosedChain.generatedPoint O hk base orientation)
          orientation (Fin.mk 0 hk) ((k - 1) + 1) v := by
          rfl
    _ =
        ClosedPlacementAlgebra.iteratedTransitionBlock O hk
          (GeneratedClosedChain.generatedPoint O hk base orientation)
          orientation (Fin.mk 0 hk) k v := by
          congr
          omega

/-- The generated final-block period equation is equivalent to algebraic
closure of the iterated-transition block from cyclic index `0`. -/
theorem generatedPeriodEquation_iff_generatedClosureEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    GeneratedPeriodEquation O hk base orientation ↔
      GeneratedClosureEquation O hk base orientation := by
  constructor
  · intro hperiod
    funext v
    calc
      ClosedPlacementAlgebra.iteratedTransitionBlock O hk
          (GeneratedClosedChain.generatedPoint O hk base orientation)
          orientation (Fin.mk 0 hk) k v =
          GeneratedClosedChain.generatedBlock O hk base orientation k v := by
            exact (generatedBlock_eq_iterated_from_zero_at_card
              O hk base orientation v).symm
      _ = base v := generatedPeriodEquation_apply O hk base orientation hperiod v
  · intro hclosure
    funext v
    calc
      GeneratedClosedChain.generatedBlock O hk base orientation k v =
          ClosedPlacementAlgebra.iteratedTransitionBlock O hk
            (GeneratedClosedChain.generatedPoint O hk base orientation)
            orientation (Fin.mk 0 hk) k v := by
            exact generatedBlock_eq_iterated_from_zero_at_card
              O hk base orientation v
      _ = base v := generatedClosureEquation_apply O hk base orientation hclosure v

/-- Convert the generated final-block period equation into algebraic closure
from cyclic index `0`. -/
theorem generatedClosureEquation_of_generatedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod : GeneratedPeriodEquation O hk base orientation) :
    GeneratedClosureEquation O hk base orientation :=
  (generatedPeriodEquation_iff_generatedClosureEquation O hk base orientation).mp
    hperiod

/-- Convert algebraic closure from cyclic index `0` back into the generated
final-block period equation. -/
theorem generatedPeriodEquation_of_generatedClosureEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hclosure : GeneratedClosureEquation O hk base orientation) :
    GeneratedPeriodEquation O hk base orientation :=
  (generatedPeriodEquation_iff_generatedClosureEquation O hk base orientation).mpr
    hclosure

end

end PeriodInterface
end PachToth
end ErdosProblems1066
