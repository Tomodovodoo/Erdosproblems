import ErdosProblems1066.Swanepoel.Arithmetic
import ErdosProblems1066.Swanepoel.LocalConfigurations
import ErdosProblems1066.UnitDistanceBounds

/-!
# Swanepoel Bridge Target

This module names the intended `8 / 31` lower-bound statement while keeping it
as data, not as a checked public result.  The imported Swanepoel modules contain
verified arithmetic and local vocabulary that can be used when the remaining
geometric and graph-theoretic layers are formalized.
-/

namespace ErdosProblems1066
namespace Swanepoel

/-- Target proposition for Swanepoel's `8 / 31` lower bound. -/
def targetLowerBoundEightThirtyOne : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Exists fun s : Finset (Fin n) => C.IsIndep s /\ 31 * s.card >= 8 * n

end Swanepoel
end ErdosProblems1066
