import ErdosProblems1066.PachToth.ExactLocalBranchSolverSurface
import ErdosProblems1066.PachToth.RoleHingeInterfaceRefinement

set_option autoImplicit false

/-!
# W12 orbit square-distance route for the concrete connector obligations

This module isolates the current status of the connector-only orbit metric
route.  The target bridge is positive once orbit-level exact-local squared
distances are supplied, but the fully quantified concrete theorem from
`TASK.md` is not provable for the present four-target concrete map: the
two-block all-same word already exposes the checked `T1_1,r` exact-base row
obstruction.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace OrbitSqDistancesW12

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real

abbrev ConcreteTransitionObligations :=
  RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations

/-- The uniform same-orientation word used by the minimal obstruction. -/
def allSameOrientation {k : Nat} : Fin k -> OrientationData.BlockOrientation :=
  fun _ => OrientationData.BlockOrientation.same

/-- Orbit-level exact-local squared distances still supply the same-block
isometry needed by the generated closed-chain interface. -/
theorem sameBlockIsometry_of_concreteTransitionObligations_orbitSqDistances
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (horbit :
      RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
        ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      ConcreteTransitionObligations hk
      BaseTransitionRealization.exactBase orientation := by
  exact
    RoleHingeInterfaceRefinement.generatedSameBlockIsometry_of_orbitSqDistances
      ConcreteTransitionObligations hk BaseTransitionRealization.exactBase
      orientation horbit

set_option linter.style.longLine false in
/-- Once closure, separation, and orbit-level exact-local squared distances are
available, the connector-only concrete obligations route to the exact-block
target without using arbitrary-source same-block preservation. -/
theorem exactBlockTarget_of_concreteTransitionObligations_orbitSqDistances
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (horbit :
      RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
        ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    RoleHingeInterfaceRefinement.targetUpperConstructionFiveSixteenAt_exactBlock_of_concreteTransitionObligations_orbitSqDistances
      hk orientation closure separated horbit

/-- The selected-transition exact-local preservation field is blocked for the
current concrete connector obligations. -/
theorem concreteTransitionObligations_transitionExactLocalSqDistances_blocked :
    Not
      (RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
        ConcreteTransitionObligations) := by
  intro htransition
  have hblock :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances
        ((ConcreteTransitionObligations.transitionFor
            OrientationData.BlockOrientation.same).placeNext
          ExactLocalGeometry.localPoint) := by
    exact
      htransition OrientationData.BlockOrientation.same
        ExactLocalGeometry.localPoint
        RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
  have hrow := hblock T1_1 LocalVertex.r
  exact
    ExactLocalTransitionObligationMatrix.samePlaceNext_exactBase_T1_1_r_forces_contradiction
      (by
        simpa [ConcreteTransitionObligations,
          RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations]
          using hrow)

/-- The live fully quantified target shape from `TASK.md` is false for the
current concrete map: in a two-block all-same word, block `1` is the same
concrete transition from the exact base, so the checked `T1_1,r` row
contradiction applies. -/
theorem concreteTransitionObligations_orbitSqDistances_twoSame_blocked :
    Not
      (RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
        ConcreteTransitionObligations (by decide : 0 < 2)
        BaseTransitionRealization.exactBase
        (allSameOrientation : Fin 2 -> OrientationData.BlockOrientation)) := by
  intro horbit
  have hblock :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances
        (GeneratedClosedChain.generatedPoint
          ConcreteTransitionObligations (by decide : 0 < 2)
          BaseTransitionRealization.exactBase
          (allSameOrientation : Fin 2 -> OrientationData.BlockOrientation)
          (Fin.mk 1 (by decide) : Fin 2)) := by
    exact horbit (Fin.mk 1 (by decide) : Fin 2)
  have hrow := hblock T1_1 LocalVertex.r
  exact
    ExactLocalTransitionObligationMatrix.samePlaceNext_exactBase_T1_1_r_forces_contradiction
      (by
        simpa [GeneratedClosedChain.generatedPoint,
          GeneratedClosedChain.generatedBlock,
          GeneratedClosedChain.orientationAt,
          allSameOrientation, ConcreteTransitionObligations,
          RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations,
          BaseTransitionRealization.exactBase] using hrow)

/-- Consequently, the theorem shape named in `TASK.md` cannot be proved for the
present concrete connector-only map without changing the map or adding
stronger orbit data that excludes the obstructed word. -/
theorem concreteTransitionObligations_orbitSqDistances_blocked :
    Not
      (forall {k : Nat} (hk : 0 < k)
        (orientation : Fin k -> OrientationData.BlockOrientation),
          RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
            ConcreteTransitionObligations hk
            BaseTransitionRealization.exactBase orientation) := by
  intro hall
  exact
    concreteTransitionObligations_orbitSqDistances_twoSame_blocked
      (hall (k := 2) (by decide)
        (allSameOrientation : Fin 2 -> OrientationData.BlockOrientation))

end OrbitSqDistancesW12
end PachToth
end ErdosProblems1066

end
