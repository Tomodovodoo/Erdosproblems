import ErdosProblems1066.Swanepoel.K23NoEarlyClosure

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# K23 minimal-failure instantiation

This file is the explicit instantiation layer between the concrete K23/local
exclusion facts and the minimal-failure no-early closure.  It keeps the
labels, turn data, and window containment data visible in every route, while
using `MinimalGraphFacts` only for the final minimal-failure eliminator
packaging.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace K23MinimalFailureInstantiation

open GraphBridge
open LateTriplesInterface
open LocalConfigurations
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete

universe u

variable {V : Type u} {G : LocalGraph V}

/-! ## Local no-early packages from K23/card exclusions -/

section Local

variable [Fintype V] [DecidableEq V]
variable {P : BrokenLatticePredicates G 8}

/-- A K23 obstruction at each early start, together with an explicit
no-`K_{2,3}` exclusion, gives the concrete five-start no-early package. -/
def concreteNoEarlyTripleEquality_of_K23Exclusion
    (H : M8ConcreteK23ObstructionInputs P)
    (hnoK23 : Not (HasK23 G)) :
    M8ConcreteNoEarlyTripleEquality P :=
  concreteNoEarlyTripleEquality_of_K23Obstruction H hnoK23

/-- A K23 obstruction at each early start, together with a no-`K_{2,3}`
exclusion, gives the construction-level no-early package for explicit local
labels. -/
def constructionNoEarlyTriples_of_K23Exclusion
    {n : Nat} {C : _root_.UDConfig n}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (hnoK23 : Not (HasK23 (unitDistanceLocalGraph C))) :
    M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples localLabels :=
  NoEarlyTripleFromLemma9.constructionNoEarlyTriples_of_concreteNoEarlyTripleEquality
    (concreteNoEarlyTripleEquality_of_K23Exclusion H hnoK23)

/-- Common-neighbor lower bounds at the five early starts, together with a
two-common-neighbor card cap, give the concrete no-early package directly. -/
def concreteNoEarlyTripleEquality_of_commonNeighborCardCap
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P)
    (hcap :
      forall {a b : V}, Not (a = b) ->
        (LocalExclusions.LocalGraph.commonNeighborFinset G a b).card <= 2) :
    M8ConcreteNoEarlyTripleEquality P :=
  H.toConcreteNoEarlyTripleEquality_of_cardCap hcap

/-- Common-neighbor lower bounds can also be routed through the K23 exclusion
view of the same local obstruction. -/
def concreteNoEarlyTripleEquality_of_commonNeighborK23Exclusion
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P)
    (hnoK23 : Not (HasK23 G)) :
    M8ConcreteNoEarlyTripleEquality P :=
  concreteNoEarlyTripleEquality_of_K23Exclusion
    H.toK23ObstructionInputs hnoK23

/-- A finite local-exclusion package is exactly the no-K23 plus card-cap row
needed by the common-neighbor-card route. -/
def concreteNoEarlyTripleEquality_of_commonNeighborFiniteLocalExclusions
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyTripleEquality P :=
  concreteNoEarlyTripleEquality_of_commonNeighborCardCap
    H E.commonNeighborCard_le_two

end Local

/-! ## Explicit turn/window packages for a fixed minimal failure -/

section FixedMinimalFailure

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The K23/no-early route with all fixed-row data explicit. -/
structure K23TurnWindowRow
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  arc : M8TurnBoundsFromArc.NonconcaveArcTurnData
  k23Obstruction :
    M8ConcreteK23ObstructionInputs localLabels.predicates.data
  noK23 : Not (HasK23 (unitDistanceLocalGraph C))
  windowContainment :
    M8WindowGeometryFromContainment.M8WindowContainment
      localLabels arc.toM8TurnBounds

namespace K23TurnWindowRow

/-- The row supplies the concrete no-early triple package. -/
def noEarlyTriples
    (D : K23TurnWindowRow C hmin) :
    M8ConcreteNoEarlyTripleEquality D.localLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_K23Exclusion
    D.k23Obstruction D.noK23

/-- The row supplies construction-level no-early triples. -/
def constructionNoEarlyTriples
    (D : K23TurnWindowRow C hmin) :
    M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples D.localLabels :=
  NoEarlyTripleFromLemma9.constructionNoEarlyTriples_of_concreteNoEarlyTripleEquality
    D.noEarlyTriples

/-- The row supplies the exact turn/window/no-early package. -/
def toTurnWindowNoEarlyPackage
    (D : K23TurnWindowRow C hmin) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin where
  localLabels := D.localLabels
  arc := D.arc
  noEarlyTriples := D.noEarlyTriples
  windowContainment := D.windowContainment

/-- Forget the explicit no-K23 proof to the existing K23 closure row. -/
def toK23NoEarlyClosureFields
    (D : K23TurnWindowRow C hmin) :
    K23NoEarlyClosure.MinimalFailureK23TurnWindowFields C hmin where
  localLabels := D.localLabels
  arc := D.arc
  k23Obstruction := D.k23Obstruction
  windowContainment := D.windowContainment

/-- The row supplies separated construction fields. -/
def toSeparatedConstructionFields
    (D : K23TurnWindowRow C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  D.toTurnWindowNoEarlyPackage.toM8SeparatedConstructionFields

/-- A fixed minimal failure carrying the explicit K23 turn/window row is
contradictory. -/
theorem contradiction
    (D : K23TurnWindowRow C hmin) :
    False :=
  D.toTurnWindowNoEarlyPackage.contradiction

end K23TurnWindowRow

/-- Minimal-failure specialization: `K23ObstructionConcrete` supplies the
no-`K_{2,3}` exclusion used by the explicit K23 row. -/
def k23TurnWindowRow_of_minimalFailure
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    K23TurnWindowRow C hmin where
  localLabels := localLabels
  arc := A
  k23Obstruction := H
  noK23 :=
    K23ObstructionConcrete.not_hasK23_of_minimalFailure_noAssumptions hmin
  windowContainment := W

/-- Minimal-failure K23 obstruction data, with labels/turn/window data
explicit, gives the turn/window/no-early package. -/
def turnWindowNoEarlyPackage_of_K23_minimalFailure
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  (k23TurnWindowRow_of_minimalFailure (hmin := hmin) A H W).toTurnWindowNoEarlyPackage

/-- The common-neighbor-card route with all fixed-row data explicit. -/
structure CommonNeighborCardTurnWindowRow
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  arc : M8TurnBoundsFromArc.NonconcaveArcTurnData
  commonNeighborObstruction :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
      localLabels.predicates.data
  commonNeighborCardCap :
    forall {a b : Fin n}, Not (a = b) ->
      (LocalExclusions.LocalGraph.commonNeighborFinset
        (unitDistanceLocalGraph C) a b).card <= 2
  windowContainment :
    M8WindowGeometryFromContainment.M8WindowContainment
      localLabels arc.toM8TurnBounds

namespace CommonNeighborCardTurnWindowRow

/-- The row supplies the concrete no-early triple package by the card-cap
route. -/
def noEarlyTriples
    (D : CommonNeighborCardTurnWindowRow C hmin) :
    M8ConcreteNoEarlyTripleEquality D.localLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_commonNeighborCardCap
    D.commonNeighborObstruction D.commonNeighborCardCap

/-- The row can be viewed as the existing common-neighbor closure row. -/
def toCommonNeighborNoEarlyClosureFields
    (D : CommonNeighborCardTurnWindowRow C hmin) :
    K23NoEarlyClosure.MinimalFailureCommonNeighborTurnWindowFields C hmin where
  localLabels := D.localLabels
  arc := D.arc
  commonNeighborObstruction := D.commonNeighborObstruction
  windowContainment := D.windowContainment

/-- The row also forgets to the explicit K23 row, using the same minimal
unit-distance K23 exclusion. -/
def toK23TurnWindowRow
    (D : CommonNeighborCardTurnWindowRow C hmin) :
    K23TurnWindowRow C hmin where
  localLabels := D.localLabels
  arc := D.arc
  k23Obstruction := D.commonNeighborObstruction.toK23ObstructionInputs
  noK23 :=
    K23ObstructionConcrete.not_hasK23_of_minimalFailure_noAssumptions hmin
  windowContainment := D.windowContainment

/-- The row supplies the exact turn/window/no-early package. -/
def toTurnWindowNoEarlyPackage
    (D : CommonNeighborCardTurnWindowRow C hmin) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin where
  localLabels := D.localLabels
  arc := D.arc
  noEarlyTriples := D.noEarlyTriples
  windowContainment := D.windowContainment

/-- The row supplies separated construction fields. -/
def toSeparatedConstructionFields
    (D : CommonNeighborCardTurnWindowRow C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  D.toTurnWindowNoEarlyPackage.toM8SeparatedConstructionFields

/-- A fixed minimal failure carrying the common-neighbor-card turn/window row
is contradictory. -/
theorem contradiction
    (D : CommonNeighborCardTurnWindowRow C hmin) :
    False :=
  D.toTurnWindowNoEarlyPackage.contradiction

end CommonNeighborCardTurnWindowRow

/-- Minimal failures inherit the common-neighbor card cap used by the explicit
common-neighbor row. -/
def commonNeighborCardTurnWindowRow_of_minimalFailure
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
        localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    CommonNeighborCardTurnWindowRow C hmin where
  localLabels := localLabels
  arc := A
  commonNeighborObstruction := H
  commonNeighborCardCap := by
    intro a b hab
    exact
      K23ObstructionConcrete.commonNeighborFinset_card_le_two_of_minimalFailure_noAssumptions
        hmin hab
  windowContainment := W

/-- Minimal-failure common-neighbor/card data, with labels/turn/window data
explicit, gives the turn/window/no-early package. -/
def turnWindowNoEarlyPackage_of_commonNeighborCard_minimalFailure
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
        localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  (commonNeighborCardTurnWindowRow_of_minimalFailure
    (hmin := hmin) A H W).toTurnWindowNoEarlyPackage

end FixedMinimalFailure

/-! ## Uniform minimal-failure eliminators -/

/-- Uniform explicit K23 rows for every minimal cleared failure. -/
def K23TurnWindowRowEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (K23TurnWindowRow C hmin)

/-- Uniform explicit common-neighbor-card rows for every minimal cleared
failure. -/
def CommonNeighborCardTurnWindowRowEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (CommonNeighborCardTurnWindowRow C hmin)

/-- Explicit K23 rows instantiate the existing `K23NoEarlyClosure`
eliminator. -/
theorem k23NoEarlyClosureEliminator_of_K23Rows
    (hbuild : K23TurnWindowRowEliminator) :
    K23NoEarlyClosure.MinimalFailureM8K23NoEarlyClosureEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D => exact Nonempty.intro D.toK23NoEarlyClosureFields

/-- Explicit common-neighbor rows instantiate the existing
common-neighbor/card closure eliminator. -/
theorem commonNeighborNoEarlyClosureEliminator_of_commonNeighborRows
    (hbuild : CommonNeighborCardTurnWindowRowEliminator) :
    K23NoEarlyClosure.MinimalFailureM8CommonNeighborNoEarlyClosureEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D => exact Nonempty.intro D.toCommonNeighborNoEarlyClosureFields

/-- Explicit common-neighbor rows also instantiate explicit K23 rows. -/
theorem K23Rows_of_commonNeighborRows
    (hbuild : CommonNeighborCardTurnWindowRowEliminator) :
    K23TurnWindowRowEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D => exact Nonempty.intro D.toK23TurnWindowRow

/-- Uniform explicit K23 rows are a `MinimalGraphFacts` eliminator. -/
theorem minimalClearedFailureEliminator_of_K23Rows
    (hbuild : K23TurnWindowRowEliminator) :
    MinimalClearedFailureEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D => exact D.contradiction

/-- Uniform explicit common-neighbor rows are a `MinimalGraphFacts`
eliminator. -/
theorem minimalClearedFailureEliminator_of_commonNeighborRows
    (hbuild : CommonNeighborCardTurnWindowRowEliminator) :
    MinimalClearedFailureEliminator :=
  minimalClearedFailureEliminator_of_K23Rows
    (K23Rows_of_commonNeighborRows hbuild)

/-- Uniform explicit K23 rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_K23Rows
    (hbuild : K23TurnWindowRowEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure
    (minimalClearedFailureEliminator_of_K23Rows hbuild)

/-- Uniform explicit common-neighbor/card rows rule out all minimal cleared
failures. -/
theorem no_minimalClearedFailure_of_commonNeighborRows
    (hbuild : CommonNeighborCardTurnWindowRowEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure
    (minimalClearedFailureEliminator_of_commonNeighborRows hbuild)

/-- Uniform explicit K23 rows clear every unit-distance configuration through
the minimal-failure principle. -/
theorem hasCleared_of_K23Rows
    (hbuild : K23TurnWindowRowEliminator) :
    forall (n : Nat) (C : _root_.UDConfig n),
      CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C :=
  MinimalGraphFacts.hasCleared_of_minimalClearedFailureEliminator
    (minimalClearedFailureEliminator_of_K23Rows hbuild)

/-- Uniform explicit common-neighbor/card rows clear every unit-distance
configuration through the minimal-failure principle. -/
theorem hasCleared_of_commonNeighborRows
    (hbuild : CommonNeighborCardTurnWindowRowEliminator) :
    forall (n : Nat) (C : _root_.UDConfig n),
      CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C :=
  MinimalGraphFacts.hasCleared_of_minimalClearedFailureEliminator
    (minimalClearedFailureEliminator_of_commonNeighborRows hbuild)

end K23MinimalFailureInstantiation
end Swanepoel
end ErdosProblems1066

end
