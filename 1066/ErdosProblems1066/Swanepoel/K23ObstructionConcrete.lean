import ErdosProblems1066.Swanepoel.NoEarlyTripleObstructionConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Concrete `K_{2,3}` obstruction inputs

This module supplies a small concrete layer in front of
`NoEarlyTripleObstructionConcrete`.

The downstream no-early route wants five implications from an early
triple-equality start to a local `K_{2,3}`.  Here we expose a graph-theoretic
common-neighbor certificate for such a `K_{2,3}`, prove that it feeds the
existing obstruction package, and route the currently available finite
unit-distance local exclusions back into the minimal-failure wrapper without
an extra `K23DegreeReducible` assumption.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace K23ObstructionConcrete

open GraphBridge
open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete

universe u

variable {V : Type u} {G : LocalGraph V}

/-! ## Concrete common-neighbor witnesses -/

/-- Three distinct common neighbors of a pair of distinct vertices. -/
structure ThreeCommonNeighborWitness
    (G : LocalGraph V) where
  left0 : V
  left1 : V
  right0 : V
  right1 : V
  right2 : V
  left_ne : left0 ≠ left1
  right01_ne : right0 ≠ right1
  right02_ne : right0 ≠ right2
  right12_ne : right1 ≠ right2
  right0_common : G.CommonNeighbor left0 left1 right0
  right1_common : G.CommonNeighbor left0 left1 right1
  right2_common : G.CommonNeighbor left0 left1 right2

namespace ThreeCommonNeighborWitness

/-- A three-common-neighbor witness is exactly a labelled `K_{2,3}` pattern. -/
def toK23Pattern (W : ThreeCommonNeighborWitness G) : K23Pattern G where
  left0 := W.left0
  left1 := W.left1
  right0 := W.right0
  right1 := W.right1
  right2 := W.right2
  left_ne := W.left_ne
  right01_ne := W.right01_ne
  right02_ne := W.right02_ne
  right12_ne := W.right12_ne
  right0_common := W.right0_common
  right1_common := W.right1_common
  right2_common := W.right2_common

/-- A three-common-neighbor witness produces `HasK23`. -/
theorem hasK23 (W : ThreeCommonNeighborWitness G) : HasK23 G :=
  Nonempty.intro (toK23Pattern W)

section Finite

variable [Fintype V] [DecidableEq V]

/-- The left vertex of a concrete `K_{2,3}` witness has degree at least
three. -/
theorem degree_left0_ge_three (W : ThreeCommonNeighborWitness G) :
    3 <= LocalExclusions.LocalGraph.degree G W.left0 :=
  LocalExclusions.LocalGraph.degree_ge_three_left0_of_K23Pattern
    G (toK23Pattern W)

/-- The other left vertex of a concrete `K_{2,3}` witness has degree at least
three. -/
theorem degree_left1_ge_three (W : ThreeCommonNeighborWitness G) :
    3 <= LocalExclusions.LocalGraph.degree G W.left1 :=
  LocalExclusions.LocalGraph.degree_ge_three_left1_of_K23Pattern
    G (toK23Pattern W)

end Finite

end ThreeCommonNeighborWitness

/-! ## Start-indexed obstruction inputs -/

/-- Concrete local data: each of the five early triple equalities produces a
three-common-neighbor witness. -/
structure M8ConcreteThreeCommonNeighborObstructionInputs
    (P : BrokenLatticePredicates G 8) where
  witness_start1 :
    P.tripleEquality start1 -> ThreeCommonNeighborWitness G
  witness_start2 :
    P.tripleEquality start2 -> ThreeCommonNeighborWitness G
  witness_start3 :
    P.tripleEquality start3 -> ThreeCommonNeighborWitness G
  witness_start4 :
    P.tripleEquality start4 -> ThreeCommonNeighborWitness G
  witness_start5 :
    P.tripleEquality start5 -> ThreeCommonNeighborWitness G

namespace M8ConcreteThreeCommonNeighborObstructionInputs

variable {P : BrokenLatticePredicates G 8}

/-- Convert concrete three-common-neighbor data into the K23 obstruction
package consumed by `NoEarlyTripleObstructionConcrete`. -/
def toK23ObstructionInputs
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P) :
    M8ConcreteK23ObstructionInputs P where
  forbidden_start1 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start1 h)
  forbidden_start2 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start2 h)
  forbidden_start3 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start3 h)
  forbidden_start4 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start4 h)
  forbidden_start5 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start5 h)

/-- Concrete three-common-neighbor data plus finite local exclusions give the
five no-early triple exclusions. -/
def toConcreteNoEarlyTripleEquality
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyTripleEquality P :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    H.toK23ObstructionInputs E

/-- Concrete three-common-neighbor data plus finite local exclusions give the
abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8NoEarlyTripleEquality P :=
  (H.toConcreteNoEarlyTripleEquality E).toNoEarlyTripleEquality

/-- Concrete three-common-neighbor data plus finite local exclusions give the
raw late-triples predicate. -/
theorem toBrokenLatticeLateTriples
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8BrokenLatticeLateTriples P :=
  (H.toConcreteNoEarlyTripleEquality E).toBrokenLatticeLateTriples

end M8ConcreteThreeCommonNeighborObstructionInputs

/-- Indexed local data: every early triple equality produces a concrete
three-common-neighbor witness. -/
structure M8EarlyThreeCommonNeighborObstructionInputs
    (P : BrokenLatticePredicates G 8) where
  witness_of_early_triple :
    forall {a : M8TripleStartIndex},
      M8TripleStartEarly a ->
        P.tripleEquality a -> ThreeCommonNeighborWitness G

namespace M8EarlyThreeCommonNeighborObstructionInputs

variable {P : BrokenLatticePredicates G 8}

/-- Restrict indexed early-start data to the five concrete starts. -/
def toConcrete
    (H : M8EarlyThreeCommonNeighborObstructionInputs P) :
    M8ConcreteThreeCommonNeighborObstructionInputs P where
  witness_start1 := H.witness_of_early_triple
    (a := start1) (by simp [M8TripleStartEarly])
  witness_start2 := H.witness_of_early_triple
    (a := start2) (by simp [M8TripleStartEarly])
  witness_start3 := H.witness_of_early_triple
    (a := start3) (by simp [M8TripleStartEarly])
  witness_start4 := H.witness_of_early_triple
    (a := start4) (by simp [M8TripleStartEarly])
  witness_start5 := H.witness_of_early_triple
    (a := start5) (by simp [M8TripleStartEarly])

/-- Indexed early-start common-neighbor data gives the K23 obstruction
package consumed downstream. -/
def toK23ObstructionInputs
    (H : M8EarlyThreeCommonNeighborObstructionInputs P) :
    M8ConcreteK23ObstructionInputs P :=
  H.toConcrete.toK23ObstructionInputs

/-- Indexed early-start common-neighbor data plus finite local exclusions give
the five no-early triple exclusions. -/
def toConcreteNoEarlyTripleEquality
    [Fintype V] [DecidableEq V]
    (H : M8EarlyThreeCommonNeighborObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyTripleEquality P :=
  H.toConcrete.toConcreteNoEarlyTripleEquality E

end M8EarlyThreeCommonNeighborObstructionInputs

/-! ## No-assumption finite-local-exclusion routes -/

/-- If the unit-distance local graph has no `K_{2,3}`, then the
`K23DegreeReducible` premise used by the older minimal-failure route is
available vacuously. -/
theorem K23DegreeReducible_of_not_hasK23
    {n : Nat} {C : _root_.UDConfig n}
    (hno : ¬ HasK23 (unitDistanceLocalGraph C)) :
    K23DegreeReducible C := by
  intro P
  exact False.elim (hno (Nonempty.intro P))

/-- A finite local-exclusion package supplies the vacuous
`K23DegreeReducible` input for the unit-distance graph. -/
theorem K23DegreeReducible_of_finiteLocalExclusionPackage
    {n : Nat} {C : _root_.UDConfig n}
    (E : FiniteLocalExclusionPackage (unitDistanceLocalGraph C)) :
    K23DegreeReducible C :=
  K23DegreeReducible_of_not_hasK23 E.noK23

/-- The already-proved unit-distance finite local exclusions provide the
degree-reducibility input required by the minimal-failure K23 wrapper. -/
theorem K23DegreeReducible_of_unitDistanceConfig
    {n : Nat} (C : _root_.UDConfig n) :
    K23DegreeReducible C :=
  K23DegreeReducible_of_finiteLocalExclusionPackage
    (finiteLocalExclusionPackage_of_unitDistanceConfig C)

/-- Minimal-failure finite local exclusions with no separate
`K23DegreeReducible` assumption. -/
def finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) :
    FiniteLocalExclusionPackage (unitDistanceLocalGraph C) :=
  finiteLocalExclusionPackage_of_minimalFailure_and_K23DegreeReducible
    hmin (K23DegreeReducible_of_unitDistanceConfig C)

/-- Minimal failures inherit the no-`K_{2,3}` exclusion without any extra
local-deletion assumption. -/
theorem not_hasK23_of_minimalFailure_noAssumptions
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) :
    ¬ HasK23 (unitDistanceLocalGraph C) :=
  (finiteLocalExclusionPackage_of_minimalFailure_noAssumptions hmin).noK23

/-- Minimal failures inherit the common-neighbor cap without any extra
local-deletion assumption. -/
theorem commonNeighborFinset_card_le_two_of_minimalFailure_noAssumptions
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) {a b : Fin n} (hab : a ≠ b) :
    (LocalExclusions.LocalGraph.commonNeighborFinset
      (unitDistanceLocalGraph C) a b).card <= 2 :=
  (finiteLocalExclusionPackage_of_minimalFailure_noAssumptions hmin).commonNeighborCard_le_two
    hab

/-! ## Direct downstream wrappers -/

/-- K23 obstruction inputs route through the existing minimal-failure
turn/window/no-early wrapper without requiring callers to provide a separate
`K23DegreeReducible` argument. -/
def turnWindowNoEarlyPackage_of_K23Obstruction_minimalFailure_noAssumptions
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  turnWindowNoEarlyPackage_of_K23Obstruction_minimalFailure
    (C := C) (hmin := hmin) (localLabels := localLabels)
    A H (K23DegreeReducible_of_unitDistanceConfig C) W

/-- Concrete three-common-neighbor obstruction data route directly into the
minimal-failure turn/window/no-early package. -/
def turnWindowNoEarlyPackage_of_threeCommonNeighborObstruction_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H :
      M8ConcreteThreeCommonNeighborObstructionInputs
        localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  turnWindowNoEarlyPackage_of_K23Obstruction_minimalFailure_noAssumptions
    A H.toK23ObstructionInputs W

/-- Indexed early-start common-neighbor obstruction data route directly into
the minimal-failure turn/window/no-early package. -/
def turnWindowNoEarlyPackage_of_earlyThreeCommonNeighborObstruction_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H :
      M8EarlyThreeCommonNeighborObstructionInputs
        localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  turnWindowNoEarlyPackage_of_threeCommonNeighborObstruction_minimalFailure
    A H.toConcrete W

end K23ObstructionConcrete
end Swanepoel
end ErdosProblems1066

end
