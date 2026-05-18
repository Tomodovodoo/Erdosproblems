import ErdosProblems1066.Swanepoel.BrokenLatticeAssemblyW13

set_option autoImplicit false

/-!
W13 broken-lattice eliminator

This file is the narrow public wrapper around `BrokenLatticeAssemblyW13`.
The only remaining input is the explicit record builder for each minimal
cleared failure.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeEliminatorW13

open BrokenLatticeAssemblyW13
open MinimalGraphFacts

noncomputable section

/-- A direct explicit-record builder rules out every minimal cleared failure. -/
theorem no_minimalClearedFailure_of_explicitRecordBuilder
    (build :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  intro n C hmin
  exact (build C hmin).contradiction

/-- A direct explicit-record builder proves the public Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_explicitRecordBuilder
    (build :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_explicitRecordBuilder build)

end

end BrokenLatticeEliminatorW13
end Swanepoel
end ErdosProblems1066
