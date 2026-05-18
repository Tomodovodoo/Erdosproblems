import ErdosProblems1066.PachToth.Bridge
import ErdosProblems1066.PachToth.GeometricSoundness
import ErdosProblems1066.PachToth.IndexedChain

/-!
# Pach--Toth Target Reduction

This file contains only a thin logical reduction: the proposition-valued
Pach--Toth target follows if every positive block count has an indexed chain
realization.  It does not construct those realizations.
-/

namespace ErdosProblems1066
namespace PachToth

/-- The in-progress target proposition follows from indexed chain
realizations for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_indexedChainRealizations
    (H :
      forall (k : Nat) (hk : 0 < k),
        IndexedChain.IndexedChainRealization k hk) :
    targetUpperConstructionFiveSixteen := by
  intro k hk
  exact IndexedChain.exists_config_with_independent_card_le_five_mul hk (H k hk)

/-- The in-progress target proposition follows from explicit geometric
edge-soundness certificates for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_explicitEdgeSoundness
    (H :
      forall (k : Nat) (hk : 0 < k),
        GeometricSoundness.ExplicitEdgeSoundness k hk) :
    targetUpperConstructionFiveSixteen := by
  apply targetUpperConstructionFiveSixteen_of_indexedChainRealizations
  intro k hk
  exact (H k hk).toIndexedChainRealization

end PachToth
end ErdosProblems1066
