import ErdosProblems1066.Swanepoel.K23ObstructionConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# K23/no-early closure from common-neighbor bounds

This file is a small closure layer for the minimal-failure K23/no-early route.
It records the exact fields still needed for a fixed turn/window row, and it
adapts start-indexed common-neighbor lower bounds to the no-early packages
consumed by the M8 pipeline.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace K23NoEarlyClosure

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

/-! ## Common-neighbor lower-bound witnesses -/

/-- A concrete pair of vertices with at least three common neighbors. -/
structure CommonNeighborCardLowerWitness
    (G : LocalGraph V) [Fintype V] [DecidableEq V] where
  left0 : V
  left1 : V
  left_ne : Not (left0 = left1)
  card_ge_three :
    3 <= (LocalExclusions.LocalGraph.commonNeighborFinset G left0 left1).card

namespace CommonNeighborCardLowerWitness

variable [Fintype V] [DecidableEq V]

/-- A three-common-neighbor lower bound produces a labelled K23 obstruction. -/
theorem hasK23 (W : CommonNeighborCardLowerWitness G) : HasK23 G :=
  LocalExclusions.LocalGraph.exists_hasK23_of_commonNeighborFinset_card_ge_three
    G W.left_ne W.card_ge_three

/-- A common-neighbor lower bound contradicts any two-common-neighbor cap. -/
theorem false_of_card_le_two
    (W : CommonNeighborCardLowerWitness G)
    (hcap :
      forall {a b : V}, Not (a = b) ->
        (LocalExclusions.LocalGraph.commonNeighborFinset G a b).card <= 2) :
    False := by
  have hge :
      3 <= (LocalExclusions.LocalGraph.commonNeighborFinset
        G W.left0 W.left1).card :=
    W.card_ge_three
  have hle := hcap W.left_ne
  omega

end CommonNeighborCardLowerWitness

/-! ## Five-start common-neighbor-card obstruction inputs -/

/-- Each early triple equality supplies a pair with at least three common
neighbors.  This is the common-neighbor-bound form of the K23 obstruction. -/
structure M8ConcreteCommonNeighborCardObstructionInputs
    (P : BrokenLatticePredicates G 8) [Fintype V] [DecidableEq V] where
  witness_start1 :
    P.tripleEquality start1 -> CommonNeighborCardLowerWitness G
  witness_start2 :
    P.tripleEquality start2 -> CommonNeighborCardLowerWitness G
  witness_start3 :
    P.tripleEquality start3 -> CommonNeighborCardLowerWitness G
  witness_start4 :
    P.tripleEquality start4 -> CommonNeighborCardLowerWitness G
  witness_start5 :
    P.tripleEquality start5 -> CommonNeighborCardLowerWitness G

namespace M8ConcreteCommonNeighborCardObstructionInputs

variable {P : BrokenLatticePredicates G 8} [Fintype V] [DecidableEq V]

/-- Convert common-neighbor lower bounds to the K23 obstruction package. -/
def toK23ObstructionInputs
    (H : M8ConcreteCommonNeighborCardObstructionInputs P) :
    M8ConcreteK23ObstructionInputs P where
  forbidden_start1 h := (H.witness_start1 h).hasK23
  forbidden_start2 h := (H.witness_start2 h).hasK23
  forbidden_start3 h := (H.witness_start3 h).hasK23
  forbidden_start4 h := (H.witness_start4 h).hasK23
  forbidden_start5 h := (H.witness_start5 h).hasK23

/-- A common-neighbor cap turns the five lower bounds into explicit
contradictions. -/
def toFalseStartImplications
    (H : M8ConcreteCommonNeighborCardObstructionInputs P)
    (hcap :
      forall {a b : V}, Not (a = b) ->
        (LocalExclusions.LocalGraph.commonNeighborFinset G a b).card <= 2) :
    M8ConcreteFalseStartImplications P where
  false_start1 h := (H.witness_start1 h).false_of_card_le_two hcap
  false_start2 h := (H.witness_start2 h).false_of_card_le_two hcap
  false_start3 h := (H.witness_start3 h).false_of_card_le_two hcap
  false_start4 h := (H.witness_start4 h).false_of_card_le_two hcap
  false_start5 h := (H.witness_start5 h).false_of_card_le_two hcap

/-- Common-neighbor lower bounds plus a common-neighbor cap give the concrete
no-early package directly. -/
def toConcreteNoEarlyTripleEquality_of_cardCap
    (H : M8ConcreteCommonNeighborCardObstructionInputs P)
    (hcap :
      forall {a b : V}, Not (a = b) ->
        (LocalExclusions.LocalGraph.commonNeighborFinset G a b).card <= 2) :
    M8ConcreteNoEarlyTripleEquality P :=
  (H.toFalseStartImplications hcap).toConcreteNoEarlyTripleEquality

/-- Finite local exclusions provide the cap needed by the direct
common-neighbor route. -/
def toConcreteNoEarlyTripleEquality
    (H : M8ConcreteCommonNeighborCardObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyTripleEquality P :=
  H.toConcreteNoEarlyTripleEquality_of_cardCap
    E.commonNeighborCard_le_two

/-- The same data as the abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    (H : M8ConcreteCommonNeighborCardObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8NoEarlyTripleEquality P :=
  (H.toConcreteNoEarlyTripleEquality E).toNoEarlyTripleEquality

/-- The same data as the raw late-triples predicate. -/
theorem toBrokenLatticeLateTriples
    (H : M8ConcreteCommonNeighborCardObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8BrokenLatticeLateTriples P :=
  (H.toConcreteNoEarlyTripleEquality E).toBrokenLatticeLateTriples

end M8ConcreteCommonNeighborCardObstructionInputs

/-! ## Fixed minimal-failure field packages -/

/-- Exact K23 turn/window fields for one fixed minimal cleared failure.

The finite local-exclusion row is intentionally absent: for a unit-distance
configuration it is supplied by the existing common-neighbor geometry. -/
structure MinimalFailureK23TurnWindowFields {n : Nat}
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  arc : M8TurnBoundsFromArc.NonconcaveArcTurnData
  k23Obstruction :
    M8ConcreteK23ObstructionInputs localLabels.predicates.data
  windowContainment :
    M8WindowGeometryFromContainment.M8WindowContainment
      localLabels arc.toM8TurnBounds

namespace MinimalFailureK23TurnWindowFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The finite local-exclusion package supplied by the unit-distance
common-neighbor cap. -/
def finiteLocalExclusions
    (_D : MinimalFailureK23TurnWindowFields C hmin) :
    FiniteLocalExclusionPackage (unitDistanceLocalGraph C) :=
  K23ObstructionConcrete.finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
    hmin

/-- Repackage the exact fields as the obstruction data used by
`NoEarlyTripleObstructionConcrete`. -/
def toK23TurnWindowObstructionData
    (D : MinimalFailureK23TurnWindowFields C hmin) :
    M8ConcreteK23TurnWindowObstructionData C hmin where
  localLabels := D.localLabels
  arc := D.arc
  k23Obstruction := D.k23Obstruction
  finiteLocalExclusions := D.finiteLocalExclusions
  windowContainment := D.windowContainment

/-- The K23 fields give the concrete no-early triple package. -/
def noEarlyTriples
    (D : MinimalFailureK23TurnWindowFields C hmin) :
    M8ConcreteNoEarlyTripleEquality D.localLabels.predicates.data :=
  D.toK23TurnWindowObstructionData.noEarlyTriples

/-- The K23 fields give the turn/window/no-early package. -/
def toTurnWindowNoEarlyPackage
    (D : MinimalFailureK23TurnWindowFields C hmin) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  D.toK23TurnWindowObstructionData.toTurnWindowNoEarlyPackage

/-- The K23 fields give separated construction fields. -/
def toSeparatedConstructionFields
    (D : MinimalFailureK23TurnWindowFields C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  D.toK23TurnWindowObstructionData.toM8SeparatedConstructionFields

/-- The K23 fields give clean construction-interface data. -/
def toM8ConstructionData
    (D : MinimalFailureK23TurnWindowFields C hmin) :
    M8ConstructionInterface.M8ConstructionData C hmin :=
  D.toK23TurnWindowObstructionData.toM8ConstructionData

/-- A fixed minimal failure satisfying the exact K23 turn/window fields is
contradictory. -/
theorem contradiction
    (D : MinimalFailureK23TurnWindowFields C hmin) :
    False :=
  D.toK23TurnWindowObstructionData.contradiction

end MinimalFailureK23TurnWindowFields

/-- Exact common-neighbor-card turn/window fields for one fixed minimal
cleared failure. -/
structure MinimalFailureCommonNeighborTurnWindowFields {n : Nat}
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  arc : M8TurnBoundsFromArc.NonconcaveArcTurnData
  commonNeighborObstruction :
    M8ConcreteCommonNeighborCardObstructionInputs
      localLabels.predicates.data
  windowContainment :
    M8WindowGeometryFromContainment.M8WindowContainment
      localLabels arc.toM8TurnBounds

namespace MinimalFailureCommonNeighborTurnWindowFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Forget common-neighbor lower bounds to the exact K23 turn/window fields. -/
def toK23TurnWindowFields
    (D : MinimalFailureCommonNeighborTurnWindowFields C hmin) :
    MinimalFailureK23TurnWindowFields C hmin where
  localLabels := D.localLabels
  arc := D.arc
  k23Obstruction := D.commonNeighborObstruction.toK23ObstructionInputs
  windowContainment := D.windowContainment

/-- Repackage common-neighbor lower bounds as K23 obstruction data. -/
def toK23TurnWindowObstructionData
    (D : MinimalFailureCommonNeighborTurnWindowFields C hmin) :
    M8ConcreteK23TurnWindowObstructionData C hmin :=
  D.toK23TurnWindowFields.toK23TurnWindowObstructionData

/-- The common-neighbor fields give the concrete no-early triple package. -/
def noEarlyTriples
    (D : MinimalFailureCommonNeighborTurnWindowFields C hmin) :
    M8ConcreteNoEarlyTripleEquality D.localLabels.predicates.data :=
  D.toK23TurnWindowFields.noEarlyTriples

/-- The common-neighbor fields give the turn/window/no-early package. -/
def toTurnWindowNoEarlyPackage
    (D : MinimalFailureCommonNeighborTurnWindowFields C hmin) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  D.toK23TurnWindowFields.toTurnWindowNoEarlyPackage

/-- The common-neighbor fields give separated construction fields. -/
def toSeparatedConstructionFields
    (D : MinimalFailureCommonNeighborTurnWindowFields C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  D.toK23TurnWindowFields.toSeparatedConstructionFields

/-- A fixed minimal failure satisfying the common-neighbor turn/window fields
is contradictory. -/
theorem contradiction
    (D : MinimalFailureCommonNeighborTurnWindowFields C hmin) :
    False :=
  D.toK23TurnWindowFields.contradiction

end MinimalFailureCommonNeighborTurnWindowFields

/-! ## Direct turn/window adapters -/

/-- Common-neighbor lower-bound obstruction data route directly into the
minimal-failure turn/window/no-early package. -/
def turnWindowNoEarlyPackage_of_commonNeighborCardObstruction_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H :
      M8ConcreteCommonNeighborCardObstructionInputs
        localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  let D : MinimalFailureCommonNeighborTurnWindowFields C hmin :=
    { localLabels := localLabels
      arc := A
      commonNeighborObstruction := H
      windowContainment := W }
  D.toTurnWindowNoEarlyPackage

/-- Common-neighbor lower-bound obstruction data route directly into the
minimal-failure K23 turn/window obstruction package. -/
def k23TurnWindowObstructionData_of_commonNeighborCardObstruction_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H :
      M8ConcreteCommonNeighborCardObstructionInputs
        localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8ConcreteK23TurnWindowObstructionData C hmin :=
  let D : MinimalFailureCommonNeighborTurnWindowFields C hmin :=
    { localLabels := localLabels
      arc := A
      commonNeighborObstruction := H
      windowContainment := W }
  D.toK23TurnWindowObstructionData

/-! ## Uniform eliminators -/

/-- Uniform exact K23 turn/window fields for every minimal failure. -/
def MinimalFailureM8K23NoEarlyClosureEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (MinimalFailureK23TurnWindowFields C hmin)

/-- Uniform common-neighbor-card fields for every minimal failure. -/
def MinimalFailureM8CommonNeighborNoEarlyClosureEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (MinimalFailureCommonNeighborTurnWindowFields C hmin)

/-- Common-neighbor-card fields imply the K23 field eliminator. -/
theorem k23NoEarlyClosureEliminator_of_commonNeighbor
    (hbuild : MinimalFailureM8CommonNeighborNoEarlyClosureEliminator) :
    MinimalFailureM8K23NoEarlyClosureEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D => exact Nonempty.intro D.toK23TurnWindowFields

/-- The exact K23 field eliminator supplies the existing K23 turn/window
eliminator. -/
theorem k23TurnWindowEliminator_of_k23NoEarlyClosureEliminator
    (hbuild : MinimalFailureM8K23NoEarlyClosureEliminator) :
    MinimalFailureM8K23TurnWindowEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro D => exact Nonempty.intro D.toK23TurnWindowObstructionData

/-- Uniform exact K23 fields rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_k23NoEarlyClosureEliminator
    (hbuild : MinimalFailureM8K23NoEarlyClosureEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_K23TurnWindowEliminator
    (k23TurnWindowEliminator_of_k23NoEarlyClosureEliminator hbuild)

/-- Uniform common-neighbor-card fields rule out all minimal cleared failures.
-/
theorem no_minimalClearedFailure_of_commonNeighborNoEarlyClosureEliminator
    (hbuild : MinimalFailureM8CommonNeighborNoEarlyClosureEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_k23NoEarlyClosureEliminator
    (k23NoEarlyClosureEliminator_of_commonNeighbor hbuild)

end K23NoEarlyClosure
end Swanepoel
end ErdosProblems1066

end
