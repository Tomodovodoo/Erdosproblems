import ErdosProblems1066.Swanepoel.MinimalGraphFacts
import ErdosProblems1066.Swanepoel.SmallIndependentNeighborhood
import ErdosProblems1066.Swanepoel.DeficientNeighborhood

set_option autoImplicit false

/-!
# Conditional minimum-degree reduction

This file derives the minimum-degree lower bound for a minimal cleared failure
from the still-external deficient-neighborhood theorem for small independent
sets.  No proof of that theorem is supplied here; it remains an explicit
hypothesis.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimumDegree

open MinimalGraphFacts
open SmallIndependentNeighborhood

noncomputable section

lemma singleton_isIndep {n : Nat} (C : _root_.UDConfig n)
    (v : Fin n) :
    C.IsIndep ({v} : Finset (Fin n)) := by
  intro i hi j hj hij _hunit
  have hi_eq : i = v := by
    simpa using hi
  have hj_eq : j = v := by
    simpa using hj
  exact hij (hi_eq.trans hj_eq.symm)

/-- For a singleton center, the outside part of the canonical closed
neighborhood is exactly the unit-distance neighbor set used by the degree
pipeline. -/
theorem outsideNeighborhoodOf_singleton_eq_unitDistanceNeighborSet
    {n : Nat} (C : _root_.UDConfig n) (center : Fin n) :
    outsideNeighborhoodOf C ({center} : Finset (Fin n)) =
      DegreePipeline.unitDistanceNeighborSet C center := by
  classical
  ext j
  rw [mem_outsideNeighborhoodOf, DegreePipeline.mem_unitDistanceNeighborSet]
  constructor
  · rintro ⟨hj_not_center, hunit⟩
    rcases hunit with ⟨u, hu, hdist⟩
    have hu_eq : u = center := by
      simpa using hu
    subst u
    refine ⟨?_, ?_⟩
    · simpa using hj_not_center
    · rw [_root_.eucDist_comm]
      exact hdist
  · rintro ⟨hj_ne_center, hdist⟩
    refine ⟨?_, ?_⟩
    · simpa using hj_ne_center
    · refine ⟨center, by simp, ?_⟩
      rw [_root_.eucDist_comm]
      exact hdist

lemma outsideNeighborhoodOf_singleton_card_eq_unitDistanceNeighborSet_card
    {n : Nat} (C : _root_.UDConfig n) (center : Fin n) :
    (outsideNeighborhoodOf C ({center} : Finset (Fin n))).card =
      (DegreePipeline.unitDistanceNeighborSet C center).card := by
  rw [outsideNeighborhoodOf_singleton_eq_unitDistanceNeighborSet]

/-- Conditional minimum-degree form: once the deficient-neighborhood theorem is
available for every small independent nonempty set in a minimal cleared
failure, every vertex has at least three unit-distance neighbors. -/
theorem unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure_of_outsideNeighborhood_bound
    (outsideNeighborhood_card_ge_three_mul_of_minimalFailure :
      forall {n : Nat} {C : _root_.UDConfig n} {S : Finset (Fin n)},
        IsMinimalClearedFailure C ->
        S.Nonempty ->
        C.IsIndep S ->
        S.card <= 8 ->
        3 * S.card <= (outsideNeighborhoodOf C S).card)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card := by
  have hsingleton :
      3 * ({v} : Finset (Fin n)).card <=
        (outsideNeighborhoodOf C ({v} : Finset (Fin n))).card :=
    outsideNeighborhood_card_ge_three_mul_of_minimalFailure
      (C := C) (S := ({v} : Finset (Fin n))) hmin
      (by exact ⟨v, by simp⟩)
      (singleton_isIndep C v)
      (by simp)
  have hthree :
      3 <= (outsideNeighborhoodOf C ({v} : Finset (Fin n))).card := by
    simpa using hsingleton
  simpa [outsideNeighborhoodOf_singleton_eq_unitDistanceNeighborSet] using
    hthree

/-- Every vertex in a minimal cleared failure has at least three unit-distance
neighbors, obtained by applying the deficient-neighborhood exclusion to a
singleton independent set. -/
theorem unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
  unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure_of_outsideNeighborhood_bound
    DeficientNeighborhood.outsideNeighborhood_card_ge_three_mul_of_minimalFailure
    hmin v

end

end MinimumDegree
end Swanepoel
end ErdosProblems1066
