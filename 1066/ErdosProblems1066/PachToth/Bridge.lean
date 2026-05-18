import ErdosProblems1066.PachToth.Chain
import ErdosProblems1066.PachToth.Coordinates
import ErdosProblems1066.UnitDistanceBounds

/-!
# Pach--Toth Bridge Target

This module names the intended `5 / 16` upper-construction statement while
keeping it as data, not as a checked public result.  The imported Pach--Toth
modules contain verified finite arithmetic, finite graph data, chain
combinatorics, and raw coordinate checks for the remaining realization work.
-/

namespace ErdosProblems1066
namespace PachToth

/-- Target proposition for the block form of the Pach--Toth `5 / 16` construction. -/
def targetUpperConstructionFiveSixteen : Prop :=
  forall (k : Nat), 0 < k ->
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k

end PachToth
end ErdosProblems1066
