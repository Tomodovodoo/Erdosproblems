import ErdosProblems1066.Swanepoel.BrokenLatticePipeline
import ErdosProblems1066.Swanepoel.BrokenLatticeClosure
import ErdosProblems1066.Swanepoel.Lemma10AnalyticBridge
import ErdosProblems1066.Swanepoel.Lemma10Pipeline
import ErdosProblems1066.Swanepoel.GeometryRemainingFieldsW10

set_option autoImplicit false

/-!
# Swanepoel W11 broken-lattice predicate fields

This file refines the final broken-lattice predicate package around the
minimal-failure honest-local-predicate input.  It keeps three layers separate:

* the local-label package and the exact
  `MinimalFailureM8HonestLocalPredicatesFacts` input used by
  `exists_m8_honestLocalPredicates_of_minimalFailure`;
* geometry-selected local labels from `GeometryRemainingFieldsW10`;
* analytic E22/E23 and late-triples fields, which are enough for the checked
  Lemma 10 contradiction.

No field is constructed from minimality alone here.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeFieldsW11

open BrokenLatticePipeline
open GraphBridge
open GeometryRemainingFieldsW10
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open LocalConfigurations
open MinimalGraphFacts

universe u

variable {n : Nat}

/-! ## Local-predicate input for the minimal-failure existential -/

/-- Exact local-predicate input for one fixed minimal cleared failure.

The `facts` field is the named input consumed by
`exists_m8_honestLocalPredicates_of_minimalFailure`; the agreement field ties
that input to the displayed local labels. -/
structure MinimalFailureLocalPredicateFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  facts : MinimalFailureM8HonestLocalPredicatesFacts C hmin
  facts_agree :
    facts.toHonestLocalPredicates = localLabels.predicates

namespace MinimalFailureLocalPredicateFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The honest local predicates displayed by the local-label field. -/
def predicates
    (L : MinimalFailureLocalPredicateFields C hmin) :
    M8HonestLocalPredicates (unitDistanceLocalGraph C) :=
  L.localLabels.predicates

/-- The underlying `p`, `q`, `r`, and `s` labels. -/
abbrev labels
    (L : MinimalFailureLocalPredicateFields C hmin) :
    BrokenLatticeLabels (Fin n) 8 :=
  L.localLabels.labels

/-- Build the exact local-predicate fields from already assembled local
labels. -/
def ofM8LocalLabels
    (localLabels : M8ConstructionInterface.M8LocalLabels C) :
    MinimalFailureLocalPredicateFields C hmin where
  localLabels := localLabels
  facts :=
    MinimalFailureM8HonestLocalPredicatesFacts.ofM8LocalLabels
      (hmin := hmin) localLabels
  facts_agree := rfl

@[simp]
theorem ofM8LocalLabels_predicates
    (localLabels : M8ConstructionInterface.M8LocalLabels C) :
    (ofM8LocalLabels (C := C) (hmin := hmin) localLabels).predicates =
      localLabels.predicates :=
  rfl

/-- The exact existential route through
`exists_m8_honestLocalPredicates_of_minimalFailure`. -/
theorem exists_via_minimalFailureFacts
    (L : MinimalFailureLocalPredicateFields C hmin) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = L.facts.toHonestLocalPredicates := by
  exact exists_m8_honestLocalPredicates_of_minimalFailure L.facts

/-- The same existential, rewritten to the displayed local-label predicates. -/
theorem exists_predicates
    (L : MinimalFailureLocalPredicateFields C hmin) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = L.predicates := by
  rcases L.exists_via_minimalFailureFacts with ⟨P, hP⟩
  exact ⟨P, hP.trans L.facts_agree⟩

/-- Forget to the older W10 broken-lattice predicate package once the analytic
and late-triples fields have been supplied. -/
def toW10BrokenLatticePredicateFields
    (L : MinimalFailureLocalPredicateFields C hmin)
    (turn : Nat -> Real)
    (turn_nonnegative : forall k : Nat, 0 <= turn k)
    (total_turn_lt_pi_div_three : totalTurn turn < Real.pi / 3)
    (figure8_E22 : HonestFigure8SeparatedWindowLowerE22 L.predicates turn)
    (figure9_E23 : HonestFigure9AdjacentWindowLowerE23 L.predicates turn)
    (lateTriples : L.predicates.LateTriples) :
    GeometryRemainingFieldsW10.BrokenLatticePredicateFields C hmin where
  predicates := L.predicates
  turn := turn
  turn_nonnegative := turn_nonnegative
  total_turn_lt_pi_div_three := total_turn_lt_pi_div_three
  figure8_E22 := figure8_E22
  figure9_E23 := figure9_E23
  lateTriples := lateTriples

end MinimalFailureLocalPredicateFields

/-! ## Geometry-selected local predicates -/

/-- The W10 geometry source row together with the exact local-predicate fact
for its boundary-derived local labels. -/
structure GeometryLocalPredicateFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  facts : MinimalFailureM8HonestLocalPredicatesFacts C hmin
  facts_agree :
    facts.toHonestLocalPredicates = source.localLabels.predicates

namespace GeometryLocalPredicateFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The local labels selected by the W10 geometry source row. -/
def localLabels
    (G : GeometryLocalPredicateFields.{u} C hmin) :
    M8ConstructionInterface.M8LocalLabels C :=
  G.source.localLabels

/-- The honest local predicates selected by the W10 geometry source row. -/
def predicates
    (G : GeometryLocalPredicateFields.{u} C hmin) :
    M8HonestLocalPredicates (unitDistanceLocalGraph C) :=
  G.source.localLabels.predicates

/-- The geometry source row viewed as the exact local-predicate input package.
-/
def toMinimalFailureLocalPredicateFields
    (G : GeometryLocalPredicateFields.{u} C hmin) :
    MinimalFailureLocalPredicateFields C hmin where
  localLabels := G.source.localLabels
  facts := G.facts
  facts_agree := G.facts_agree

/-- Build geometry-local-predicate fields from a W10 geometry source row. -/
def ofGeometrySourceFields
    (source : GeometrySourceFields.{u} C hmin) :
    GeometryLocalPredicateFields.{u} C hmin where
  source := source
  facts :=
    MinimalFailureM8HonestLocalPredicatesFacts.ofM8LocalLabels
      (hmin := hmin) source.localLabels
  facts_agree := rfl

@[simp]
theorem ofGeometrySourceFields_localLabels
    (source : GeometrySourceFields.{u} C hmin) :
    (ofGeometrySourceFields (C := C) (hmin := hmin) source).localLabels =
      source.localLabels :=
  rfl

/-- The minimal-failure existential specialized to the geometry-selected
local labels. -/
theorem exists_predicates
    (G : GeometryLocalPredicateFields.{u} C hmin) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = G.predicates := by
  exact G.toMinimalFailureLocalPredicateFields.exists_predicates

end GeometryLocalPredicateFields

/-! ## E22/E23 plus late-triples fields -/

/-- Exact analytic fields for the local predicates selected by
`MinimalFailureLocalPredicateFields`.

This is the first layer in this file that is contradictory: E22, E23, the turn
budget, and late triples are all explicit fields. -/
structure E22E23LocalPredicateFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localPredicates : MinimalFailureLocalPredicateFields C hmin
  turnBounds : M8ConstructionInterface.M8TurnBounds
  figure8_E22 :
    HonestFigure8SeparatedWindowLowerE22
      localPredicates.predicates turnBounds.turn
  figure9_E23 :
    HonestFigure9AdjacentWindowLowerE23
      localPredicates.predicates turnBounds.turn
  lateTriples : localPredicates.predicates.LateTriples

namespace E22E23LocalPredicateFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The honest local predicates carried by this analytic package. -/
def predicates
    (E : E22E23LocalPredicateFields C hmin) :
    M8HonestLocalPredicates (unitDistanceLocalGraph C) :=
  E.localPredicates.predicates

/-- The selected turn function. -/
def turn
    (E : E22E23LocalPredicateFields C hmin) :
    Nat -> Real :=
  E.turnBounds.turn

/-- Repackage as the W10 exact broken-lattice predicate fields. -/
def toW10BrokenLatticePredicateFields
    (E : E22E23LocalPredicateFields C hmin) :
    GeometryRemainingFieldsW10.BrokenLatticePredicateFields C hmin :=
  E.localPredicates.toW10BrokenLatticePredicateFields E.turn
    E.turnBounds.turn_nonnegative
    E.turnBounds.total_turn_lt_pi_div_three
    E.figure8_E22 E.figure9_E23 E.lateTriples

/-- Repackage as the older broken-lattice minimal-failure construction data.
-/
def toBrokenLatticeConstructionData
    (E : E22E23LocalPredicateFields C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  E.toW10BrokenLatticePredicateFields.toBrokenLatticeConstructionData

/-- The analytic E22/E23 package contradicts the fixed minimal failure. -/
theorem contradiction
    (E : E22E23LocalPredicateFields C hmin) :
    False := by
  exact Lemma10AnalyticBridge.honestContradiction_of_E22_E23
    E.predicates E.turn
    E.turnBounds.turn_nonnegative
    E.turnBounds.total_turn_lt_pi_div_three
    E.figure8_E22 E.figure9_E23 E.lateTriples

/-- Equivalent contradiction routed through `Lemma10Pipeline` after converting
E22/E23 into turn-force hypotheses. -/
theorem contradiction_via_turnPipeline
    (E : E22E23LocalPredicateFields C hmin) :
    False := by
  exact Lemma10Pipeline.honestContradiction_of_turn_hypotheses
    E.predicates E.turn
    E.turnBounds.turn_nonnegative
    E.turnBounds.total_turn_lt_pi_div_three
    (separatedFailuresForceTurn_of_m8_E22 E.figure8_E22)
    (adjacentFailuresForceTurn_of_m8_E23 E.figure9_E23)
    E.lateTriples

end E22E23LocalPredicateFields

/-! ## Geometry-selected E22/E23 fields -/

/-- Geometry-selected local predicates together with containment-derived
E22/E23 and an explicit late-triples field. -/
structure GeometryE22E23PredicateFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localPredicates : GeometryLocalPredicateFields.{u} C hmin
  containment : ContainmentFields localPredicates.source
  lateTriples : localPredicates.predicates.LateTriples

namespace GeometryE22E23PredicateFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The E22 projection supplied by the W10 containment fields. -/
theorem figure8_E22
    (G : GeometryE22E23PredicateFields.{u} C hmin) :
    HonestFigure8SeparatedWindowLowerE22
      G.localPredicates.predicates G.localPredicates.source.turnBounds.turn :=
  G.containment.E22_E23.1

/-- The E23 projection supplied by the W10 containment fields. -/
theorem figure9_E23
    (G : GeometryE22E23PredicateFields.{u} C hmin) :
    HonestFigure9AdjacentWindowLowerE23
      G.localPredicates.predicates G.localPredicates.source.turnBounds.turn :=
  G.containment.E22_E23.2

/-- Forget the geometry-selected fields to the direct analytic package. -/
def toE22E23LocalPredicateFields
    (G : GeometryE22E23PredicateFields.{u} C hmin) :
    E22E23LocalPredicateFields C hmin where
  localPredicates := G.localPredicates.toMinimalFailureLocalPredicateFields
  turnBounds := G.localPredicates.source.turnBounds
  figure8_E22 := G.figure8_E22
  figure9_E23 := G.figure9_E23
  lateTriples := G.lateTriples

/-- Geometry-selected containment plus late triples contradicts the fixed
minimal failure. -/
theorem contradiction
    (G : GeometryE22E23PredicateFields.{u} C hmin) :
    False :=
  G.toE22E23LocalPredicateFields.contradiction

end GeometryE22E23PredicateFields

/-! ## Packages that still record remaining fields -/

/-- Direct W10 geometry fields, with the local-predicate existential input
kept visible.  The direct no-start/no-early fields are still recorded as the
source of late triples. -/
structure DirectGeometryPredicateFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localPredicates : GeometryLocalPredicateFields.{u} C hmin
  containment : ContainmentFields localPredicates.source
  noStartNoEarly : NoStartNoEarlyFields localPredicates.source

namespace DirectGeometryPredicateFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget to the W10 direct geometry package. -/
def toDirectGeometryPackage
    (D : DirectGeometryPredicateFields.{u} C hmin) :
    DirectGeometryPackage.{u} C hmin where
  source := D.localPredicates.source
  containment := D.containment
  noStartNoEarly := D.noStartNoEarly

/-- The direct W10 fields supply the geometry-selected E22/E23 package. -/
def toGeometryE22E23PredicateFields
    (D : DirectGeometryPredicateFields.{u} C hmin) :
    GeometryE22E23PredicateFields.{u} C hmin where
  localPredicates := D.localPredicates
  containment := D.containment
  lateTriples :=
    D.toDirectGeometryPackage.toBrokenLatticePredicateFields.lateTriples

/-- Direct W10 geometry fields contradict the fixed minimal failure. -/
theorem contradiction
    (D : DirectGeometryPredicateFields.{u} C hmin) :
    False :=
  D.toGeometryE22E23PredicateFields.contradiction

end DirectGeometryPredicateFields

/-- K23-derived W10 geometry fields, retaining the K23/no-early source field
honestly instead of hiding it inside the final late-triples predicate. -/
structure K23GeometryPredicateFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localPredicates : GeometryLocalPredicateFields.{u} C hmin
  containment : ContainmentFields localPredicates.source
  k23NoEarly : K23NoEarlyFields localPredicates.source

namespace K23GeometryPredicateFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget to the W10 K23 geometry package. -/
def toK23GeometryPackage
    (K : K23GeometryPredicateFields.{u} C hmin) :
    K23GeometryPackage.{u} C hmin where
  source := K.localPredicates.source
  containment := K.containment
  k23NoEarly := K.k23NoEarly

/-- K23-derived fields can be viewed as the direct package after converting
K23 no-early fields to no-start/no-early fields. -/
def toDirectGeometryPredicateFields
    (K : K23GeometryPredicateFields.{u} C hmin) :
    DirectGeometryPredicateFields.{u} C hmin where
  localPredicates := K.localPredicates
  containment := K.containment
  noStartNoEarly := K.k23NoEarly.toNoStartNoEarlyFields

/-- K23-derived W10 geometry fields contradict the fixed minimal failure. -/
theorem contradiction
    (K : K23GeometryPredicateFields.{u} C hmin) :
    False :=
  K.toDirectGeometryPredicateFields.contradiction

end K23GeometryPredicateFields

/-- Common-neighbor-derived W10 geometry fields, retaining the
common-neighbor obstruction as the remaining source field. -/
structure CommonNeighborGeometryPredicateFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localPredicates : GeometryLocalPredicateFields.{u} C hmin
  containment : ContainmentFields localPredicates.source
  commonNeighborNoEarly :
    CommonNeighborNoEarlyFields localPredicates.source

namespace CommonNeighborGeometryPredicateFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget to the W10 common-neighbor geometry package. -/
def toCommonNeighborGeometryPackage
    (K : CommonNeighborGeometryPredicateFields.{u} C hmin) :
    CommonNeighborGeometryPackage.{u} C hmin where
  source := K.localPredicates.source
  containment := K.containment
  commonNeighborNoEarly := K.commonNeighborNoEarly

/-- Common-neighbor fields can be viewed as K23-derived fields via the checked
common-neighbor-to-K23 adapter. -/
def toK23GeometryPredicateFields
    (K : CommonNeighborGeometryPredicateFields.{u} C hmin) :
    K23GeometryPredicateFields.{u} C hmin where
  localPredicates := K.localPredicates
  containment := K.containment
  k23NoEarly := K.commonNeighborNoEarly.toK23NoEarlyFields

/-- Common-neighbor-derived W10 geometry fields contradict the fixed minimal
failure. -/
theorem contradiction
    (K : CommonNeighborGeometryPredicateFields.{u} C hmin) :
    False :=
  K.toK23GeometryPredicateFields.contradiction

end CommonNeighborGeometryPredicateFields

end BrokenLatticeFieldsW11
end Swanepoel
end ErdosProblems1066

end
