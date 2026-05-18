import ErdosProblems1066.Swanepoel.NoEarlyK23AssemblyW10
import ErdosProblems1066.Swanepoel.K23NoEarlyClosure
import ErdosProblems1066.Swanepoel.K23ObstructionConcrete
import ErdosProblems1066.Swanepoel.K23MinimalFailureInstantiation
import ErdosProblems1066.Swanepoel.GeometryRemainingFieldsW10

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 K23/common-neighbor obstruction rows

This layer keeps the missing geometric inputs explicit.  A row carries the
exact W10 geometry source, the matching containment fields, and either K23
obstruction data or common-neighbor-card obstruction data for the same local
labels.  The declarations below only repackage those fields into the checked
W10 and K23/no-early closure interfaces.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace K23CommonNeighborW11

open K23MinimalFailureInstantiation
open MinimalGraphFacts
open NoEarlyTripleObstructionConcrete

universe u

variable {n : Nat}

/-! ## Pointwise W10 obstruction fields -/

/-- Exact W10 fields still needed for the K23 obstruction route. -/
structure K23ObstructionW10Fields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  k23Obstruction :
    M8ConcreteK23ObstructionInputs source.localLabels.predicates.data

namespace K23ObstructionW10Fields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Project the K23 row to the W10 K23/no-early fields. -/
def toK23NoEarlyFields
    (R : K23ObstructionW10Fields.{u} C hmin) :
    GeometryRemainingFieldsW10.K23NoEarlyFields R.source where
  k23Obstruction := R.k23Obstruction

/-- Project the K23 row to the W10 K23 geometry package. -/
def toK23GeometryPackage
    (R : K23ObstructionW10Fields.{u} C hmin) :
    GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.toK23NoEarlyFields

/-- Project the K23 row to the checked K23 closure fields. -/
def toK23NoEarlyClosureFields
    (R : K23ObstructionW10Fields.{u} C hmin) :
    K23NoEarlyClosure.MinimalFailureK23TurnWindowFields C hmin where
  localLabels := R.source.localLabels
  arc := R.source.arc
  k23Obstruction := R.k23Obstruction
  windowContainment := R.containment.windowContainment

/-- Project the K23 row to the checked turn/window row. -/
def toK23TurnWindowRow
    (R : K23ObstructionW10Fields.{u} C hmin) :
    K23TurnWindowRow C hmin where
  localLabels := R.source.localLabels
  arc := R.source.arc
  k23Obstruction := R.k23Obstruction
  noK23 :=
    K23ObstructionConcrete.not_hasK23_of_minimalFailure_noAssumptions hmin
  windowContainment := R.containment.windowContainment

/-- Project the K23 row to the W10 no-early/K23 assembly row. -/
def toAssemblyK23ObstructionRow
    (R : K23ObstructionW10Fields.{u} C hmin) :
    NoEarlyK23AssemblyW10.MinimalFailureK23ObstructionRow C hmin where
  labels := R.source.labels
  arc := R.source.arc
  k23Obstruction := R.k23Obstruction
  windowContainment := R.containment.windowContainment

/-- Project the K23 row to broken-lattice predicate fields through W10. -/
def toBrokenLatticePredicateFields
    (R : K23ObstructionW10Fields.{u} C hmin) :
    GeometryRemainingFieldsW10.BrokenLatticePredicateFields C hmin :=
  R.toK23GeometryPackage.toBrokenLatticePredicateFields

/-- A fixed K23 W11 row closes through the checked W10 K23 package. -/
theorem contradiction
    (R : K23ObstructionW10Fields.{u} C hmin) :
    False :=
  R.toK23GeometryPackage.contradiction

end K23ObstructionW10Fields

/-- Exact W10 fields still needed for the common-neighbor-card route. -/
structure CommonNeighborObstructionW10Fields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin
  containment : GeometryRemainingFieldsW10.ContainmentFields source
  commonNeighborObstruction :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
      source.localLabels.predicates.data

namespace CommonNeighborObstructionW10Fields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Project the common-neighbor row to the W10 common-neighbor fields. -/
def toCommonNeighborNoEarlyFields
    (R : CommonNeighborObstructionW10Fields.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields R.source where
  commonNeighborObstruction := R.commonNeighborObstruction

/-- Project the common-neighbor row to the W10 common-neighbor package. -/
def toCommonNeighborGeometryPackage
    (R : CommonNeighborObstructionW10Fields.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.toCommonNeighborNoEarlyFields

/-- Forget common-neighbor-card fields to the K23 W11 field row. -/
def toK23ObstructionW10Fields
    (R : CommonNeighborObstructionW10Fields.{u} C hmin) :
    K23ObstructionW10Fields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.commonNeighborObstruction.toK23ObstructionInputs

/-- Project the common-neighbor row to the checked common-neighbor closure
fields. -/
def toCommonNeighborNoEarlyClosureFields
    (R : CommonNeighborObstructionW10Fields.{u} C hmin) :
    K23NoEarlyClosure.MinimalFailureCommonNeighborTurnWindowFields C hmin where
  localLabels := R.source.localLabels
  arc := R.source.arc
  commonNeighborObstruction := R.commonNeighborObstruction
  windowContainment := R.containment.windowContainment

/-- Project the common-neighbor row to the checked turn/window row. -/
def toCommonNeighborCardTurnWindowRow
    (R : CommonNeighborObstructionW10Fields.{u} C hmin) :
    CommonNeighborCardTurnWindowRow C hmin where
  localLabels := R.source.localLabels
  arc := R.source.arc
  commonNeighborObstruction := R.commonNeighborObstruction
  commonNeighborCardCap := by
    intro a b hab
    exact
      K23ObstructionConcrete.commonNeighborFinset_card_le_two_of_minimalFailure_noAssumptions
        hmin hab
  windowContainment := R.containment.windowContainment

/-- Project the common-neighbor row to the W10 no-early/K23 assembly row. -/
def toAssemblyCommonNeighborObstructionRow
    (R : CommonNeighborObstructionW10Fields.{u} C hmin) :
    NoEarlyK23AssemblyW10.MinimalFailureCommonNeighborObstructionRow C hmin where
  labels := R.source.labels
  arc := R.source.arc
  commonNeighborObstruction := R.commonNeighborObstruction
  windowContainment := R.containment.windowContainment

/-- Project the common-neighbor row to the W10 assembly K23 row. -/
def toAssemblyK23ObstructionRow
    (R : CommonNeighborObstructionW10Fields.{u} C hmin) :
    NoEarlyK23AssemblyW10.MinimalFailureK23ObstructionRow C hmin :=
  R.toK23ObstructionW10Fields.toAssemblyK23ObstructionRow

/-- Project the common-neighbor row to broken-lattice predicate fields through
W10. -/
def toBrokenLatticePredicateFields
    (R : CommonNeighborObstructionW10Fields.{u} C hmin) :
    GeometryRemainingFieldsW10.BrokenLatticePredicateFields C hmin :=
  R.toCommonNeighborGeometryPackage.toBrokenLatticePredicateFields

/-- A fixed common-neighbor W11 row closes through the checked W10 package. -/
theorem contradiction
    (R : CommonNeighborObstructionW10Fields.{u} C hmin) :
    False :=
  R.toCommonNeighborGeometryPackage.contradiction

end CommonNeighborObstructionW10Fields

/-! ## Uniform row families -/

/-- Uniform K23 obstruction W11 rows for every minimal cleared failure. -/
structure K23ObstructionW10RowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23ObstructionW10Fields.{u} C hmin

namespace K23ObstructionW10RowFamily

/-- Project K23 W11 rows to W10 K23 geometry package rows. -/
def toK23GeometryPackageRows
    (H : K23ObstructionW10RowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin :=
  fun C hmin => (H.row C hmin).toK23GeometryPackage

/-- Project K23 W11 rows to checked K23 closure fields. -/
def toK23NoEarlyClosureEliminator
    (H : K23ObstructionW10RowFamily.{u}) :
    K23NoEarlyClosure.MinimalFailureM8K23NoEarlyClosureEliminator := by
  intro n C hmin
  exact Nonempty.intro (H.row C hmin).toK23NoEarlyClosureFields

/-- Project K23 W11 rows to checked K23 turn/window rows. -/
def toK23TurnWindowRowEliminator
    (H : K23ObstructionW10RowFamily.{u}) :
    K23TurnWindowRowEliminator := by
  intro n C hmin
  exact Nonempty.intro (H.row C hmin).toK23TurnWindowRow

/-- Project K23 W11 rows to the W10 assembly row family. -/
def toAssemblyK23ObstructionRowFamily
    (H : K23ObstructionW10RowFamily.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureK23ObstructionRowFamily where
  row := fun C hmin => (H.row C hmin).toAssemblyK23ObstructionRow

/-- K23 W11 rows give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (H : K23ObstructionW10RowFamily.{u}) :
    MinimalClearedFailureEliminator :=
  NoEarlyK23AssemblyW10.minimalClearedFailureEliminator_of_k23ObstructionRows
    H.toAssemblyK23ObstructionRowFamily

/-- K23 W11 rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : K23ObstructionW10RowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure H.minimalClearedFailureEliminator

end K23ObstructionW10RowFamily

/-- Uniform common-neighbor-card W11 rows for every minimal cleared failure. -/
structure CommonNeighborObstructionW10RowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborObstructionW10Fields.{u} C hmin

namespace CommonNeighborObstructionW10RowFamily

/-- Project common-neighbor W11 rows to W10 common-neighbor geometry package
rows. -/
def toCommonNeighborGeometryPackageRows
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u} C hmin :=
  fun C hmin => (H.row C hmin).toCommonNeighborGeometryPackage

/-- Forget common-neighbor W11 rows to K23 W11 rows. -/
def toK23ObstructionW10RowFamily
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    K23ObstructionW10RowFamily.{u} where
  row := fun C hmin => (H.row C hmin).toK23ObstructionW10Fields

/-- Project common-neighbor W11 rows to checked common-neighbor closure
fields. -/
def toCommonNeighborNoEarlyClosureEliminator
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    K23NoEarlyClosure.MinimalFailureM8CommonNeighborNoEarlyClosureEliminator := by
  intro n C hmin
  exact Nonempty.intro (H.row C hmin).toCommonNeighborNoEarlyClosureFields

/-- Project common-neighbor W11 rows to checked K23 closure fields. -/
def toK23NoEarlyClosureEliminator
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    K23NoEarlyClosure.MinimalFailureM8K23NoEarlyClosureEliminator :=
  H.toK23ObstructionW10RowFamily.toK23NoEarlyClosureEliminator

/-- Project common-neighbor W11 rows to checked common-neighbor turn/window
rows. -/
def toCommonNeighborCardTurnWindowRowEliminator
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    CommonNeighborCardTurnWindowRowEliminator := by
  intro n C hmin
  exact Nonempty.intro (H.row C hmin).toCommonNeighborCardTurnWindowRow

/-- Project common-neighbor W11 rows to the W10 assembly family. -/
def toAssemblyCommonNeighborObstructionRowFamily
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureCommonNeighborObstructionRowFamily where
  row := fun C hmin =>
    (H.row C hmin).toAssemblyCommonNeighborObstructionRow

/-- Project common-neighbor W11 rows to the W10 assembly K23 family. -/
def toAssemblyK23ObstructionRowFamily
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureK23ObstructionRowFamily :=
  H.toK23ObstructionW10RowFamily.toAssemblyK23ObstructionRowFamily

/-- Common-neighbor W11 rows give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    MinimalClearedFailureEliminator :=
  NoEarlyK23AssemblyW10.minimalClearedFailureEliminator_of_commonNeighborObstructionRows
    H.toAssemblyCommonNeighborObstructionRowFamily

/-- Common-neighbor W11 rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure H.minimalClearedFailureEliminator

end CommonNeighborObstructionW10RowFamily

/-! ## Top-level theorem forms -/

theorem minimalClearedFailureEliminator_of_k23W10Rows
    (H : K23ObstructionW10RowFamily.{u}) :
    MinimalClearedFailureEliminator :=
  H.minimalClearedFailureEliminator

theorem minimalClearedFailureEliminator_of_commonNeighborW10Rows
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    MinimalClearedFailureEliminator :=
  H.minimalClearedFailureEliminator

theorem no_minimalClearedFailure_of_k23W10Rows
    (H : K23ObstructionW10RowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.no_minimalClearedFailure

theorem no_minimalClearedFailure_of_commonNeighborW10Rows
    (H : CommonNeighborObstructionW10RowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.no_minimalClearedFailure

end K23CommonNeighborW11
end Swanepoel
end ErdosProblems1066

end
