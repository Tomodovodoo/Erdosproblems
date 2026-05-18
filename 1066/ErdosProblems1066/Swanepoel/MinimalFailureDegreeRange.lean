import ErdosProblems1066.Swanepoel.MinimumDegree
import ErdosProblems1066.Swanepoel.DegreeBound

/-!
# Minimal-failure unit-distance degree range

This module packages the already proved lower and upper bounds for the
unit-distance neighbor set of a vertex in a minimal cleared failure.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureDegreeRange

open MinimalGraphFacts

noncomputable section

/-- In a minimal cleared failure, every vertex has at least three
unit-distance neighbors. -/
theorem unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
  MinimumDegree.unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure
    hmin v

/-- Every unit-distance neighbor set has at most six vertices. -/
theorem unitDistanceNeighborSet_card_le_six
    {n : Nat} (C : _root_.UDConfig n) (v : Fin n) :
    (DegreePipeline.unitDistanceNeighborSet C v).card <= 6 := by
  simpa [DegreePipeline.unitDistanceNeighborSet] using
    DegreeBound.UDConfig.unitDistanceNeighborSet_card_le_six C v

/-- In a minimal cleared failure, every vertex has between three and six
unit-distance neighbors. -/
theorem unitDistanceNeighborSet_card_between_three_and_six_of_minimalClearedFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card ∧
      (DegreePipeline.unitDistanceNeighborSet C v).card <= 6 :=
  ⟨unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure hmin v,
    unitDistanceNeighborSet_card_le_six C v⟩

end

end MinimalFailureDegreeRange
end Swanepoel
end ErdosProblems1066
