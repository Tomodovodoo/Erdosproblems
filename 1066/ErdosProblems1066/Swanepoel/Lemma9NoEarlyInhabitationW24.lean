import ErdosProblems1066.Swanepoel.K23CommonNeighborW11
import ErdosProblems1066.Swanepoel.K23ObstructionConcrete
import ErdosProblems1066.Swanepoel.Lemma9NoEarlyConcreteW23

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W24 Lemma 9 no-early/K23 inhabitation interface

This file records the exact no-early obstruction package still needed for the
Lemma 9 finite-natural input.  The package has four concrete entry points:

* five explicit false-start contradictions;
* indexed early-start obstructions;
* five `K_{2,3}` implications plus finite local exclusions;
* five common-neighbor-card lower bounds plus finite local exclusions.

It is equivalent to the W22 `M8NatLateTripleInputs` side, and it has direct
bridges from the existing K23/common-neighbor/turn-window rows.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9NoEarlyInhabitationW24

open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete

universe u

variable {V : Type u} {G : LocalGraph V}
variable {P : BrokenLatticePredicates G 8}

/-! ## Pointwise obstruction package -/

/-- The exact obstruction package for the Lemma 9 no-early side.

The first two constructors are purely no-early bookkeeping.  The last two are
the local-geometry routes: K23 or common-neighbor lower bounds, together with
the finite local-exclusion package that turns those local patterns into
contradictions. -/
inductive M8ConcreteNoEarlyObstructionPackage
    (P : BrokenLatticePredicates G 8) [Fintype V] [DecidableEq V] : Prop
  | falseStart :
      M8ConcreteFalseStartImplications P ->
        M8ConcreteNoEarlyObstructionPackage P
  | indexed :
      M8ConcreteIndexedObstructionInputs P ->
        M8ConcreteNoEarlyObstructionPackage P
  | k23 :
      M8ConcreteK23ObstructionInputs P ->
        FiniteLocalExclusionPackage G ->
          M8ConcreteNoEarlyObstructionPackage P
  | commonNeighbor :
      K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P ->
        FiniteLocalExclusionPackage G ->
          M8ConcreteNoEarlyObstructionPackage P

namespace M8ConcreteNoEarlyObstructionPackage

variable [Fintype V] [DecidableEq V]

/-- Forget any route to the concrete five-start no-early package. -/
def toConcreteNoEarlyTripleEquality
    (H : M8ConcreteNoEarlyObstructionPackage P) :
    M8ConcreteNoEarlyTripleEquality P := by
  cases H with
  | falseStart Hfalse =>
      exact Hfalse.toConcreteNoEarlyTripleEquality
  | indexed Hindexed =>
      exact Hindexed.toConcreteNoEarlyTripleEquality
  | k23 Hk23 E =>
      exact
        concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
          Hk23 E
  | commonNeighbor Hcommon E =>
      exact Hcommon.toConcreteNoEarlyTripleEquality E

/-- Forget any route to the explicit false-start form. -/
def toFalseStartImplications
    (H : M8ConcreteNoEarlyObstructionPackage P) :
    M8ConcreteFalseStartImplications P :=
  M8ConcreteFalseStartImplications.ofConcreteNoEarlyTripleEquality
    H.toConcreteNoEarlyTripleEquality

/-- Forget any route to the abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    (H : M8ConcreteNoEarlyObstructionPackage P) :
    M8NoEarlyTripleEquality P :=
  H.toConcreteNoEarlyTripleEquality.toNoEarlyTripleEquality

/-- Forget any route to raw late triples. -/
theorem toBrokenLatticeLateTriples
    (H : M8ConcreteNoEarlyObstructionPackage P) :
    M8BrokenLatticeLateTriples P :=
  H.toConcreteNoEarlyTripleEquality.toBrokenLatticeLateTriples

/-- Any obstruction route supplies the W22 finite natural-index Lemma 9
input. -/
def toNatLateTripleInputs
    (H : M8ConcreteNoEarlyObstructionPackage P) :
    M8NatLateTripleInputs P :=
  Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_concreteNoEarlyTripleEquality
    H.toConcreteNoEarlyTripleEquality

/-- Any obstruction route supplies the indexed-obstruction view. -/
def toIndexedObstructionInputs
    (H : M8ConcreteNoEarlyObstructionPackage P) :
    M8ConcreteIndexedObstructionInputs P :=
  Lemma9NatLateTripleInhabitationW22.indexedObstructionInputs_of_natLateTripleInputs
    H.toNatLateTripleInputs

/-- The obstruction package is exactly the concrete no-early package. -/
theorem iff_concreteNoEarlyTripleEquality :
    M8ConcreteNoEarlyObstructionPackage P <->
      M8ConcreteNoEarlyTripleEquality P := by
  constructor
  case mp =>
    intro H
    exact H.toConcreteNoEarlyTripleEquality
  case mpr =>
    intro H
    exact M8ConcreteNoEarlyObstructionPackage.falseStart
      (M8ConcreteFalseStartImplications.ofConcreteNoEarlyTripleEquality H)

/-- The obstruction package is exactly the explicit false-start package. -/
theorem iff_falseStartImplications :
    M8ConcreteNoEarlyObstructionPackage P <->
      M8ConcreteFalseStartImplications P := by
  constructor
  case mp =>
    intro H
    exact H.toFalseStartImplications
  case mpr =>
    intro H
    exact M8ConcreteNoEarlyObstructionPackage.falseStart H

/-- The obstruction package is exactly inhabited indexed early-obstruction
data. -/
theorem iff_indexedObstructionInputs :
    M8ConcreteNoEarlyObstructionPackage P <->
      Nonempty (M8ConcreteIndexedObstructionInputs P) := by
  constructor
  case mp =>
    intro H
    exact Nonempty.intro H.toIndexedObstructionInputs
  case mpr =>
    intro H
    cases H with
    | intro Hindexed =>
        exact M8ConcreteNoEarlyObstructionPackage.indexed Hindexed

/-- The obstruction package is exactly the abstract no-early predicate. -/
theorem iff_noEarlyTripleEquality :
    M8ConcreteNoEarlyObstructionPackage P <->
      M8NoEarlyTripleEquality P := by
  constructor
  case mp =>
    intro H
    exact H.toNoEarlyTripleEquality
  case mpr =>
    intro H
    exact
      M8ConcreteNoEarlyObstructionPackage.falseStart
        ((Lemma9NoEarlyConcreteW23.noEarlyTripleEquality_iff_falseStartImplications
            (P := P)).mp H)

/-- The obstruction package is exactly the W22 finite natural-index Lemma 9
input. -/
theorem iff_natLateTripleInputs :
    M8ConcreteNoEarlyObstructionPackage P <->
      Nonempty (M8NatLateTripleInputs P) := by
  constructor
  case mp =>
    intro H
    exact Nonempty.intro H.toNatLateTripleInputs
  case mpr =>
    intro H
    exact
      M8ConcreteNoEarlyObstructionPackage.falseStart
        ((Lemma9NatLateTripleInhabitationW22.nonempty_natLateTripleInputs_iff_falseStartImplications
            (P := P)).mp H)

end M8ConcreteNoEarlyObstructionPackage

/-! ## Direct W22 routes -/

/-- Direct route from the W24 obstruction package into W22
`M8NatLateTripleInputs`. -/
def natLateTripleInputs_from_obstructionPackage
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteNoEarlyObstructionPackage P) :
    M8NatLateTripleInputs P :=
  H.toNatLateTripleInputs

/-- W22 finite-natural data is equivalent to the W24 obstruction package. -/
theorem nonempty_natLateTripleInputs_iff_obstructionPackage
    [Fintype V] [DecidableEq V] :
    Nonempty (M8NatLateTripleInputs P) <->
      M8ConcreteNoEarlyObstructionPackage P := by
  exact (M8ConcreteNoEarlyObstructionPackage.iff_natLateTripleInputs
    (P := P)).symm

/-- Three-common-neighbor obstruction data route into the W22 finite-natural
input through K23. -/
def natLateTripleInputs_from_threeCommonNeighborObstruction
    [Fintype V] [DecidableEq V]
    (H : K23ObstructionConcrete.M8ConcreteThreeCommonNeighborObstructionInputs
      P)
    (E : FiniteLocalExclusionPackage G) :
    M8NatLateTripleInputs P :=
  (M8ConcreteNoEarlyObstructionPackage.k23 H.toK23ObstructionInputs E)
    |>.toNatLateTripleInputs

/-- Indexed early-start three-common-neighbor data route into the W22
finite-natural input through K23. -/
def natLateTripleInputs_from_earlyThreeCommonNeighborObstruction
    [Fintype V] [DecidableEq V]
    (H : K23ObstructionConcrete.M8EarlyThreeCommonNeighborObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8NatLateTripleInputs P :=
  natLateTripleInputs_from_threeCommonNeighborObstruction H.toConcrete E

/-! ## Fixed minimal-failure turn/window packages -/

/-- The exact fixed-row package needed to combine an obstruction route with
the arc-turn-window route. -/
structure M8ConcreteNoEarlyRouteTurnWindowPackage {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  arc : M8TurnBoundsFromArc.NonconcaveArcTurnData
  obstruction :
    M8ConcreteNoEarlyObstructionPackage localLabels.predicates.data
  windowContainment :
    M8WindowGeometryFromContainment.M8WindowContainment
      localLabels arc.toM8TurnBounds

namespace M8ConcreteNoEarlyRouteTurnWindowPackage

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The fixed turn/window package supplies the W22 finite-natural Lemma 9
input for its local labels. -/
def natLateTripleInputs
    (D : M8ConcreteNoEarlyRouteTurnWindowPackage C hmin) :
    M8NatLateTripleInputs D.localLabels.predicates.data :=
  D.obstruction.toNatLateTripleInputs

/-- The fixed turn/window package supplies concrete no-early triples. -/
def noEarlyTriples
    (D : M8ConcreteNoEarlyRouteTurnWindowPackage C hmin) :
    M8ConcreteNoEarlyTripleEquality D.localLabels.predicates.data :=
  D.obstruction.toConcreteNoEarlyTripleEquality

/-- Forget the route tag after deriving no-early triples. -/
def toTurnWindowNoEarlyPackage
    (D : M8ConcreteNoEarlyRouteTurnWindowPackage C hmin) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin where
  localLabels := D.localLabels
  arc := D.arc
  noEarlyTriples := D.noEarlyTriples
  windowContainment := D.windowContainment

/-- The route-turn-window package supplies separated construction fields. -/
def toM8SeparatedConstructionFields
    (D : M8ConcreteNoEarlyRouteTurnWindowPackage C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  D.toTurnWindowNoEarlyPackage.toM8SeparatedConstructionFields

/-- The route-turn-window package supplies clean construction data. -/
def toM8ConstructionData
    (D : M8ConcreteNoEarlyRouteTurnWindowPackage C hmin) :
    M8ConstructionInterface.M8ConstructionData C hmin :=
  D.toTurnWindowNoEarlyPackage.toM8ConstructionData

/-- A fixed minimal failure with the route-turn-window package is
contradictory. -/
theorem contradiction
    (D : M8ConcreteNoEarlyRouteTurnWindowPackage C hmin) :
    False :=
  D.toTurnWindowNoEarlyPackage.contradiction

end M8ConcreteNoEarlyRouteTurnWindowPackage

/-! ## Bridges from existing K23/common-neighbor packages -/

/-- Existing K23 turn/window obstruction data instantiate the W24
route-turn-window package. -/
def routeTurnWindowPackage_from_K23TurnWindowObstructionData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8ConcreteNoEarlyRouteTurnWindowPackage C hmin where
  localLabels := D.localLabels
  arc := D.arc
  obstruction :=
    M8ConcreteNoEarlyObstructionPackage.k23
      D.k23Obstruction D.finiteLocalExclusions
  windowContainment := D.windowContainment

/-- Existing K23 turn/window obstruction data supply W22 finite-natural
inputs. -/
def natLateTripleInputs_from_K23TurnWindowObstructionData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : M8ConcreteK23TurnWindowObstructionData C hmin) :
    M8NatLateTripleInputs D.localLabels.predicates.data :=
  (routeTurnWindowPackage_from_K23TurnWindowObstructionData D)
    |>.natLateTripleInputs

/-- Existing minimal-failure K23 closure fields instantiate the W24
route-turn-window package. -/
def routeTurnWindowPackage_from_minimalFailureK23Fields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : K23NoEarlyClosure.MinimalFailureK23TurnWindowFields C hmin) :
    M8ConcreteNoEarlyRouteTurnWindowPackage C hmin :=
  routeTurnWindowPackage_from_K23TurnWindowObstructionData
    D.toK23TurnWindowObstructionData

/-- Existing minimal-failure K23 closure fields supply W22 finite-natural
inputs. -/
def natLateTripleInputs_from_minimalFailureK23Fields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : K23NoEarlyClosure.MinimalFailureK23TurnWindowFields C hmin) :
    M8NatLateTripleInputs D.localLabels.predicates.data :=
  D.toK23TurnWindowObstructionData
    |> natLateTripleInputs_from_K23TurnWindowObstructionData

/-- Existing minimal-failure common-neighbor closure fields instantiate the
W24 route-turn-window package. -/
def routeTurnWindowPackage_from_minimalFailureCommonNeighborFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D :
      K23NoEarlyClosure.MinimalFailureCommonNeighborTurnWindowFields
        C hmin) :
    M8ConcreteNoEarlyRouteTurnWindowPackage C hmin where
  localLabels := D.localLabels
  arc := D.arc
  obstruction :=
    M8ConcreteNoEarlyObstructionPackage.commonNeighbor
      D.commonNeighborObstruction
      D.toK23TurnWindowFields.finiteLocalExclusions
  windowContainment := D.windowContainment

/-- Existing minimal-failure common-neighbor closure fields supply W22
finite-natural inputs. -/
def natLateTripleInputs_from_minimalFailureCommonNeighborFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D :
      K23NoEarlyClosure.MinimalFailureCommonNeighborTurnWindowFields
        C hmin) :
    M8NatLateTripleInputs D.localLabels.predicates.data :=
  (routeTurnWindowPackage_from_minimalFailureCommonNeighborFields D)
    |>.natLateTripleInputs

/-- W11 K23/common-neighbor rows already contain exactly the K23
turn-window fields, hence they supply W22 finite-natural inputs. -/
def natLateTripleInputs_from_K23ObstructionW10Fields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (R : K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin) :
    M8NatLateTripleInputs R.source.localLabels.predicates.data :=
  natLateTripleInputs_from_minimalFailureK23Fields
    R.toK23NoEarlyClosureFields

/-- W11 common-neighbor rows already contain exactly the common-neighbor
turn-window fields, hence they supply W22 finite-natural inputs. -/
def natLateTripleInputs_from_CommonNeighborObstructionW10Fields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (R :
      K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u}
        C hmin) :
    M8NatLateTripleInputs R.source.localLabels.predicates.data :=
  natLateTripleInputs_from_minimalFailureCommonNeighborFields
    R.toCommonNeighborNoEarlyClosureFields

end Lemma9NoEarlyInhabitationW24
end Swanepoel
end ErdosProblems1066

end
