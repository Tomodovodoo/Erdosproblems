import ErdosProblems1066.Swanepoel.BrokenLatticeMinimalFailure
import ErdosProblems1066.Swanepoel.BrokenLatticePipeline
import ErdosProblems1066.Swanepoel.FigureSelectedWitnessInhabitationW25
import ErdosProblems1066.Swanepoel.LaneProductFinalGateW25
import ErdosProblems1066.Swanepoel.Lemma8FrameRowsInhabitationW25
import ErdosProblems1066.Swanepoel.Lemma9NoEarlyObstructionInhabitationW25
import ErdosProblems1066.Swanepoel.MinimalBoundaryTopologyWitnessInhabitationW25
import ErdosProblems1066.Swanepoel.PointwiseSourceFieldsInhabitationW25

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W26 broken-lattice construction from minimal-failure rows

This worker file keeps the broken-lattice construction honest.  It does not
assert a new geometric existence principle.  Instead it proves that the
already assembled W17 pointwise row, and the W20/W25 source packages that
produce such rows, give the exact `M8ConstructionData` consumed by the
existing minimal-failure broken-lattice contradiction.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeMinimalFailureConstructionW26

open BrokenLatticeMinimalFailure
open BrokenLatticePipeline
open GraphBridge
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open MinimalGraphFacts
open PointwiseRemainingRowAssemblyW17

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-! ## Pointwise-row bridge to the broken-lattice interface -/

/-- The W17 pointwise row already contains the honest local predicates needed
by `BrokenLatticePipeline.exists_m8_honestLocalPredicates_of_minimalFailure`.
-/
def localPredicatesFactsOfPointwiseRow
    (R : PointwiseW16AssemblyInputs.{u} C hmin) :
    MinimalFailureM8HonestLocalPredicatesFacts C hmin :=
  MinimalFailureM8HonestLocalPredicatesFacts.ofHonestLocalPredicates
    R.localLabels.predicates

/-- The named broken-lattice-pipeline target, discharged from a concrete W17
pointwise row rather than from an abstract placeholder.
-/
theorem exists_m8_honestLocalPredicates_of_pointwiseRow
    (R : PointwiseW16AssemblyInputs.{u} C hmin) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = (localPredicatesFactsOfPointwiseRow R).toHonestLocalPredicates :=
  BrokenLatticePipeline.exists_m8_honestLocalPredicates_of_minimalFailure
    (localPredicatesFactsOfPointwiseRow R)

/-- The W17 pointwise row contains all seven fields of the hard
`BrokenLatticeMinimalFailure.M8ConstructionData` package:

* honest local predicates from the Lemma 8 label row;
* nonnegative turn bounds and total turn below `pi / 3` from the long arc;
* Figure 8/E22 and Figure 9/E23 from the W15/W16 window fields;
* Lemma 9 late triples from the no-early/five-start row.
-/
def m8ConstructionDataOfPointwiseRow
    (R : PointwiseW16AssemblyInputs.{u} C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin where
  predicates := R.localLabels.predicates
  turn := R.turnBounds.turn
  turn_nonnegative := R.turnBounds.turn_nonnegative
  total_turn_lt_pi_div_three := R.turnBounds.total_turn_lt_pi_div_three
  figure8_E22 := R.figure8_E22
  figure9_E23 := by
    exact (R.toLemma89WindowContainmentFields.E22_E23).2
  lateTriples := by
    exact R.toLemma89Base.honestLateTriples

/-- The same row closes the minimal-failure contradiction through the
minimal-failure broken-lattice package.
-/
theorem contradiction_of_pointwiseRow
    (R : PointwiseW16AssemblyInputs.{u} C hmin) :
    False :=
  (m8ConstructionDataOfPointwiseRow R).contradiction

/-- A uniform W17 pointwise family is exactly strong enough to be the
construction-data eliminator required by `BrokenLatticeMinimalFailure`.
-/
def m8ConstructionEliminatorOfPointwiseFamily
    (F : PointwiseW16AssemblyFamily.{0}) :
    MinimalFailureM8ConstructionEliminator := by
  intro n C hmin
  exact Nonempty.intro (m8ConstructionDataOfPointwiseRow (F.row C hmin))

theorem no_minimalClearedFailure_of_pointwiseFamily
    (F : PointwiseW16AssemblyFamily.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  BrokenLatticeMinimalFailure.no_minimalClearedFailure_of_m8ConstructionEliminator
    (m8ConstructionEliminatorOfPointwiseFamily F)

theorem targetLowerBoundEightThirtyOne_of_pointwiseFamily
    (F : PointwiseW16AssemblyFamily.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalGraphFacts.hasCleared_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_pointwiseFamily F)

/-! ## W20/W25 source packages feed the pointwise-row bridge -/

abbrev W25PointwiseSourceFamilyFields : Type 1 :=
  PointwiseSourceFieldsInhabitationW25.PointwiseSourceFamilyFields.{0}

abbrev W25W20SourcePackage : Type 1 :=
  PointwiseSourceFieldsInhabitationW25.W20SourcePackage.{0}

abbrev W25ConcreteComponentLanes : Type 1 :=
  PointwiseSourceFieldsInhabitationW25.ConcreteComponentLanes.{0}

abbrev W25NamedConcreteComponentLanes : Type 1 :=
  PointwiseSourceFieldsInhabitationW25.NamedConcreteComponentLanes.{0}

def pointwiseFamilyOfW25PointwiseSourceFamilyFields
    (P : W25PointwiseSourceFamilyFields) :
    PointwiseW16AssemblyFamily.{0} :=
  P.toPointwiseW16AssemblyFamily

def m8ConstructionEliminatorOfW25PointwiseSourceFamilyFields
    (P : W25PointwiseSourceFamilyFields) :
    MinimalFailureM8ConstructionEliminator :=
  m8ConstructionEliminatorOfPointwiseFamily
    (pointwiseFamilyOfW25PointwiseSourceFamilyFields P)

theorem no_minimalClearedFailure_of_w25PointwiseSourceFamilyFields
    (P : W25PointwiseSourceFamilyFields) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_pointwiseFamily
    (pointwiseFamilyOfW25PointwiseSourceFamilyFields P)

theorem targetLowerBoundEightThirtyOne_of_w25PointwiseSourceFamilyFields
    (P : W25PointwiseSourceFamilyFields) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_pointwiseFamily
    (pointwiseFamilyOfW25PointwiseSourceFamilyFields P)

def w25PointwiseSourceFamilyFieldsOfW20SourcePackage
    (P : W25W20SourcePackage) :
    W25PointwiseSourceFamilyFields :=
  PointwiseSourceFieldsInhabitationW25.pointwiseSourceFamilyFieldsOfW20SourcePackage
    P

def m8ConstructionEliminatorOfW20SourcePackage
    (P : W25W20SourcePackage) :
    MinimalFailureM8ConstructionEliminator :=
  m8ConstructionEliminatorOfW25PointwiseSourceFamilyFields
    (w25PointwiseSourceFamilyFieldsOfW20SourcePackage P)

theorem no_minimalClearedFailure_of_w20SourcePackage
    (P : W25W20SourcePackage) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_w25PointwiseSourceFamilyFields
    (w25PointwiseSourceFamilyFieldsOfW20SourcePackage P)

theorem targetLowerBoundEightThirtyOne_of_w20SourcePackage
    (P : W25W20SourcePackage) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_w25PointwiseSourceFamilyFields
    (w25PointwiseSourceFamilyFieldsOfW20SourcePackage P)

def w25PointwiseSourceFamilyFieldsOfConcreteComponentLanes
    (P : W25ConcreteComponentLanes) :
    W25PointwiseSourceFamilyFields :=
  PointwiseSourceFieldsInhabitationW25.pointwiseSourceFamilyFieldsOfConcreteComponentLanes
    P

def w25PointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes
    (P : W25NamedConcreteComponentLanes) :
    W25PointwiseSourceFamilyFields :=
  PointwiseSourceFieldsInhabitationW25.pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes
    P

theorem no_minimalClearedFailure_of_concreteComponentLanes
    (P : W25ConcreteComponentLanes) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_w25PointwiseSourceFamilyFields
    (w25PointwiseSourceFamilyFieldsOfConcreteComponentLanes P)

theorem no_minimalClearedFailure_of_namedConcreteComponentLanes
    (P : W25NamedConcreteComponentLanes) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_w25PointwiseSourceFamilyFields
    (w25PointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes P)

theorem targetLowerBoundEightThirtyOne_of_concreteComponentLanes
    (P : W25ConcreteComponentLanes) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_w25PointwiseSourceFamilyFields
    (w25PointwiseSourceFamilyFieldsOfConcreteComponentLanes P)

theorem targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes
    (P : W25NamedConcreteComponentLanes) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_w25PointwiseSourceFamilyFields
    (w25PointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes P)

/-! ## Explicit decomposition boundary for the still-conditional route -/

/-- The tight W26 boundary: once the W20 pointwise source fields are supplied,
the broken-lattice construction-data eliminator follows.  The W25 worker
modules decompose these fields further into no-cut/topology, Lemma 8, Lemma 9,
and Figure witness obligations.
-/
theorem m8ConstructionEliminator_of_nonempty_w25PointwiseSourceFamilyFields
    (h : Nonempty W25PointwiseSourceFamilyFields) :
    MinimalFailureM8ConstructionEliminator := by
  cases h with
  | intro P =>
      exact m8ConstructionEliminatorOfW25PointwiseSourceFamilyFields P

/-- Equivalent contradiction form of the W26 boundary for any fixed minimal
failure.
-/
theorem contradiction_of_nonempty_w25PointwiseSourceFamilyFields
    (h : Nonempty W25PointwiseSourceFamilyFields)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) :
    False :=
  BrokenLatticeMinimalFailure.contradiction_of_m8ConstructionEliminator
    (m8ConstructionEliminator_of_nonempty_w25PointwiseSourceFamilyFields h)
    hmin

end

end BrokenLatticeMinimalFailureConstructionW26
end Swanepoel

namespace Verified

open Swanepoel.BrokenLatticeMinimalFailureConstructionW26

abbrev SwanepoelW26BrokenLatticePointwiseSourceFamilyFields : Type 1 :=
  W25PointwiseSourceFamilyFields

theorem swanepoelW26_m8ConstructionEliminator_of_pointwiseSourceFamilyFields
    (h : Nonempty SwanepoelW26BrokenLatticePointwiseSourceFamilyFields) :
    Swanepoel.BrokenLatticeMinimalFailure.MinimalFailureM8ConstructionEliminator :=
  m8ConstructionEliminator_of_nonempty_w25PointwiseSourceFamilyFields h

theorem lower_bound_eight_thirty_one_of_swanepoelW26_pointwiseSourceFamilyFields
    (P : SwanepoelW26BrokenLatticePointwiseSourceFamilyFields)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_w25PointwiseSourceFamilyFields P n C

end Verified
end ErdosProblems1066
