import ErdosProblems1066.UnitDistanceBounds

/-!
# Kernel-Checked Bounds

This module is the public theorem facade. It exposes only unconditional bounds
whose proof terms are present in this Lean project.

The Swanepoel `8 / 31` lower bound and Pach--Toth `5 / 16` upper
construction are tracked by conditional internal W30 gate surfaces.  Those
theorems still require explicit source-package inhabitants, so they are not
declared here as public unconditional wrappers.
-/

namespace ErdosProblems1066

namespace Verified

/-- Explicit equilateral-triangle construction giving the `1 / 3` upper bound. -/
theorem upper_bound_third (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (3 * k) =>
      forall s : Finset (Fin (3 * k)), C.IsIndep s -> s.card <= k :=
  _root_.upper_bound_third k hk

/-- Pollack/Pach quarter lower bound for unit-distance configurations. -/
theorem lower_bound_quarter (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) => C.IsIndep s /\ 4 * s.card >= n :=
  _root_.lower_bound_quarter n C

end Verified

namespace PollackPach

/-- Source-specific alias for the verified quarter lower bound. -/
theorem lower_bound_quarter (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) => C.IsIndep s /\ 4 * s.card >= n :=
  Verified.lower_bound_quarter n C

end PollackPach

end ErdosProblems1066
