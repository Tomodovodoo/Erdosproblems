import ErdosProblems1066.PachToth.OrbitSqDistancesW12
import ErdosProblems1066.PachToth.PeriodInterface
import ErdosProblems1066.PachToth.ExactLocalTransitionObligationMatrix

set_option autoImplicit false

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace TransitionAlternativeW13

open FiniteGraph
open FiniteGraph.LocalVertex
open ErdosProblems1066.PachToth.ExactLocalTransitionObligationMatrix

abbrev R2 := Prod Real Real

abbrev ConcreteTransitionObligations :
    Figure2Certificate.SameOppositeTransitionObligations :=
  OrbitSqDistancesW12.ConcreteTransitionObligations

abbrev ConcreteOrbitSqDistances {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
    ConcreteTransitionObligations hk
    BaseTransitionRealization.exactBase orientation

theorem concreteTransitionObligations_firstStep_exactBase_blocked
    (orientation : OrientationData.BlockOrientation) :
    Not
      (RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances
        ((ConcreteTransitionObligations.transitionFor orientation).placeNext
          BaseTransitionRealization.exactBase)) := by
  intro hblock
  have hrow := hblock T1_1 LocalVertex.r
  cases orientation with
  | same =>
      exact
        samePlaceNext_exactBase_T1_1_r_forces_contradiction
          (by
            simpa [ConcreteTransitionObligations,
              OrbitSqDistancesW12.ConcreteTransitionObligations,
              RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations,
              BaseTransitionRealization.exactBase] using hrow)
  | opposite =>
      exact
        oppositePlaceNext_exactBase_T1_1_r_forces_contradiction
          (by
            simpa [ConcreteTransitionObligations,
              OrbitSqDistancesW12.ConcreteTransitionObligations,
              RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations,
              BaseTransitionRealization.exactBase] using hrow)

theorem concreteTransitionObligations_transitionFixesExactBase_blocked
    (orientation : OrientationData.BlockOrientation) :
    Not
      (((ConcreteTransitionObligations.transitionFor orientation).placeNext
          BaseTransitionRealization.exactBase) =
        BaseTransitionRealization.exactBase) := by
  intro hfix
  apply concreteTransitionObligations_firstStep_exactBase_blocked orientation
  rw [hfix]
  simpa [BaseTransitionRealization.exactBase] using
    RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances

theorem concreteTransitionObligations_orbitSqDistances_nontrivial_blocked
    {k : Nat} (hk : 0 < k) (hcard : 1 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    Not (ConcreteOrbitSqDistances hk orientation) := by
  intro horbit
  let i : Fin k := Fin.mk 1 hcard
  have hblock := horbit i
  have hfirst :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances
        ((ConcreteTransitionObligations.transitionFor
            (GeneratedClosedChain.orientationAt hk orientation 0)).placeNext
          BaseTransitionRealization.exactBase) := by
    simpa [i, ConcreteOrbitSqDistances,
      RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances,
      GeneratedClosedChain.generatedPoint,
      GeneratedClosedChain.generatedBlock] using hblock
  exact
    concreteTransitionObligations_firstStep_exactBase_blocked
      (GeneratedClosedChain.orientationAt hk orientation 0) hfirst

theorem concreteTransitionObligations_oneBlock_period_blocked
    (hk : 0 < 1)
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :
    Not
      (PeriodInterface.GeneratedPeriodEquation
        ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation) := by
  intro hperiod
  have hfix :
      ((ConcreteTransitionObligations.transitionFor
          (GeneratedClosedChain.orientationAt hk orientation 0)).placeNext
        BaseTransitionRealization.exactBase) =
        BaseTransitionRealization.exactBase := by
    simpa [PeriodInterface.GeneratedPeriodEquation,
      GeneratedClosedChain.generatedBlock] using hperiod
  exact
    concreteTransitionObligations_transitionFixesExactBase_blocked
      (GeneratedClosedChain.orientationAt hk orientation 0) hfix

theorem concreteTransitionObligations_oneBlock_closure_blocked
    (hk : 0 < 1)
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :
    Not
      (PeriodInterface.GeneratedClosureEquation
        ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation) := by
  intro hclosure
  exact
    concreteTransitionObligations_oneBlock_period_blocked hk orientation
      (PeriodInterface.generatedPeriodEquation_of_generatedClosureEquation
        ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation hclosure)

theorem concreteTransitionObligations_closure_and_orbit_blocked
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    Not
      (And
        (PeriodInterface.GeneratedClosureEquation
          ConcreteTransitionObligations hk
          BaseTransitionRealization.exactBase orientation)
        (ConcreteOrbitSqDistances hk orientation)) := by
  intro hdata
  by_cases hcard : 1 < k
  case pos =>
    exact
      concreteTransitionObligations_orbitSqDistances_nontrivial_blocked
        hk hcard orientation hdata.2
  case neg =>
    have hk_eq : k = 1 := by
      exact Nat.le_antisymm (Nat.le_of_not_gt hcard) (Nat.succ_le_of_lt hk)
    subst k
    exact
      concreteTransitionObligations_oneBlock_closure_blocked
        hk orientation hdata.1

theorem concreteTransitionObligations_restrictedExactBlockRoute_blocked
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    Not
      (And
        (PeriodInterface.GeneratedClosureEquation
          ConcreteTransitionObligations hk
          BaseTransitionRealization.exactBase orientation)
        (And
          (GeneratedSeparationInterface.GeneratedGlobalSeparation
            ConcreteTransitionObligations hk
            BaseTransitionRealization.exactBase orientation)
          (ConcreteOrbitSqDistances hk orientation))) := by
  intro hdata
  exact
    concreteTransitionObligations_closure_and_orbit_blocked
      hk orientation (And.intro hdata.1 hdata.2.2)

end TransitionAlternativeW13
end PachToth
end ErdosProblems1066

end
