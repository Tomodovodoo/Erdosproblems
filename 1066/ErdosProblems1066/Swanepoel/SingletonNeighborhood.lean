import ErdosProblems1066.Swanepoel.SmallIndependentNeighborhood
import ErdosProblems1066.Swanepoel.DegreePipeline

/-!
# Singleton closed-neighborhood bridge

This module records the canonical singleton cases connecting the finite-set
neighborhoods used for small independent neighborhoods with the unit
neighborhoods used by the degree pipeline.
-/

namespace ErdosProblems1066
namespace Swanepoel

noncomputable section

/-- The canonical closed neighborhood of a singleton is the degree-pipeline
closed unit-neighborhood of its center. -/
@[simp]
theorem closedNeighborhoodOf_singleton_eq_closedUnitNeighborhood {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) :
    SmallIndependentNeighborhood.closedNeighborhoodOf C
        ({center} : Finset (Fin n)) =
      DegreePipeline.closedUnitNeighborhood C center := by
  ext v
  rw [SmallIndependentNeighborhood.mem_closedNeighborhoodOf]
  by_cases hv : v = center <;>
    simp [DegreePipeline.closedUnitNeighborhood,
      DegreePipeline.unitDistanceNeighborSet, hv, _root_.eucDist_comm]

/-- The outside part of the canonical singleton closed neighborhood is exactly
the degree-pipeline unit-distance neighbor set. -/
@[simp]
theorem outsideNeighborhoodOf_singleton_eq_unitDistanceNeighborSet {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) :
    SmallIndependentNeighborhood.outsideNeighborhoodOf C
        ({center} : Finset (Fin n)) =
      DegreePipeline.unitDistanceNeighborSet C center := by
  ext v
  rw [SmallIndependentNeighborhood.mem_outsideNeighborhoodOf]
  by_cases hv : v = center <;>
    simp [DegreePipeline.unitDistanceNeighborSet, hv, _root_.eucDist_comm]

end

end Swanepoel
end ErdosProblems1066
