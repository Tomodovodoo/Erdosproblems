import ErdosProblems1066.PachToth.SplitArbitraryNNonRigidBridge
import ErdosProblems1066.PachToth.SplitRealizationFinal
import ErdosProblems1066.PachToth.CrossBlockUpperTriangleConcrete
import ErdosProblems1066.PachToth.RoleHingeFiniteFamilyBridge

set_option autoImplicit false

/-!
# Exact and arbitrary `5 / 16` route matrix

This module is a Lean-level routing table for the currently checked
conditional Pach--Toth `5 / 16` facades.  It does not add geometric data.
Instead, each row records how one input shape proves both the exact
`16 * k` target and the arbitrary-`n` target, using the newest non-rigid,
split, and finite-table wrappers.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactFiveSixteenRouteMatrix

open SplitRealizationFinal
open SplitArbitraryNNonRigidBridge

universe u

noncomputable section

/-- One route row: the same input shape supplies the exact target and the
arbitrary target. -/
structure RouteRow (alpha : Sort u) where
  exactTarget : alpha -> targetUpperConstructionFiveSixteen
  arbitraryTarget : alpha -> targetUpperConstructionFiveSixteenArbitrary

/-- Input for the finite-index cross-block lower-bound route. -/
structure CrossBlockLowerBoundsInput where
  family : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily
  lowerBounds : CrossBlockLowerBoundsInterface.CrossBlockLowerBounds family

/-- Input for the upper-triangle polynomial table route. -/
structure UpperTrianglePolynomialTableInput where
  family : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily
  tables : CrossBlockSqTableSearch.UpperTrianglePolynomialTableFamily family

/-- Input for the upper-triangle square-value table route. -/
structure UpperTriangleSqValueTableInput where
  family : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily
  tables : CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily family

/-- The route matrix.  Rows are deliberately conditional: a row says how to
turn that row's explicit data shape into the exact and arbitrary targets. -/
structure Matrix where
  exactTarget :
    RouteRow targetUpperConstructionFiveSixteen
  nonRigidClosedPlacements :
    RouteRow
      (forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk)
  nonRigidComponents :
    RouteRow
      (forall (k : Nat) (hk : 0 < k),
        ClosedPlacementNonRigidComponents.Components k hk)
  finiteSearchFamily :
    RouteRow FiniteSearchCertificate.RoleHingedFiniteSearchFamily
  transitionFactsFiniteSearchFamily :
    RouteRow
      RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily
  crossBlockLowerBounds :
    RouteRow CrossBlockLowerBoundsInput
  upperTrianglePolynomialTables :
    RouteRow UpperTrianglePolynomialTableInput
  upperTriangleSqValueTables :
    RouteRow UpperTriangleSqValueTableInput
  vectorConcreteCrossBlock :
    RouteRow CrossBlockUpperTriangleConcrete.VectorConcreteCrossBlockFamily
  listConcreteCrossBlock :
    RouteRow CrossBlockUpperTriangleConcrete.ListConcreteCrossBlockFamily

/-- The checked conditional route matrix. -/
def matrix : Matrix where
  exactTarget :=
    { exactTarget := fun Hexact => Hexact
      arbitraryTarget := fun Hexact =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_remainderFarApart
          Hexact }
  nonRigidClosedPlacements :=
    { exactTarget := fun H =>
        NonRigidClosedPlacementInterface.targetUpperConstructionFiveSixteen_of_closedPlacements
          H
      arbitraryTarget := fun H =>
        targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
          H }
  nonRigidComponents :=
    { exactTarget := fun H =>
        ClosedPlacementNonRigidComponents.targetUpperConstructionFiveSixteen_of_components
          H
      arbitraryTarget := fun H =>
        targetUpperConstructionFiveSixteenArbitrary_of_components
          H }
  finiteSearchFamily :=
    { exactTarget := fun F =>
        F.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun F =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_remainderFarApart
          F.targetUpperConstructionFiveSixteen }
  transitionFactsFiniteSearchFamily :=
    { exactTarget := fun F =>
        F.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun F =>
        targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_remainderFarApart
          F.targetUpperConstructionFiveSixteen }
  crossBlockLowerBounds :=
    { exactTarget := fun I =>
        I.lowerBounds.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.lowerBounds.targetUpperConstructionFiveSixteenArbitrary }
  upperTrianglePolynomialTables :=
    { exactTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteenArbitrary }
  upperTriangleSqValueTables :=
    { exactTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun I =>
        I.tables.targetUpperConstructionFiveSixteenArbitrary }
  vectorConcreteCrossBlock :=
    { exactTarget := fun C =>
        C.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun C =>
        C.targetUpperConstructionFiveSixteenArbitrary }
  listConcreteCrossBlock :=
    { exactTarget := fun C =>
        C.targetUpperConstructionFiveSixteen
      arbitraryTarget := fun C =>
        C.targetUpperConstructionFiveSixteenArbitrary }

/-- The exact-target row exposed from the route matrix. -/
theorem targetUpperConstructionFiveSixteen_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteen :=
  matrix.exactTarget.exactTarget Hexact

/-- Exact-to-arbitrary split route, exposed from the route matrix. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactTarget.arbitraryTarget Hexact

/-- Exact target from checked non-rigid closed placements. -/
theorem targetUpperConstructionFiveSixteen_of_nonRigidClosedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteen :=
  matrix.nonRigidClosedPlacements.exactTarget H

/-- Arbitrary target from checked non-rigid closed placements via the split
route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_nonRigidClosedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.nonRigidClosedPlacements.arbitraryTarget H

/-- Exact target from concrete non-rigid component fields. -/
theorem targetUpperConstructionFiveSixteen_of_nonRigidComponents
    (H :
      forall (k : Nat) (hk : 0 < k),
        ClosedPlacementNonRigidComponents.Components k hk) :
    targetUpperConstructionFiveSixteen :=
  matrix.nonRigidComponents.exactTarget H

/-- Arbitrary target from concrete non-rigid component fields via the split
route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_nonRigidComponents
    (H :
      forall (k : Nat) (hk : 0 < k),
        ClosedPlacementNonRigidComponents.Components k hk) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.nonRigidComponents.arbitraryTarget H

/-- Exact target from a finite search family. -/
theorem targetUpperConstructionFiveSixteen_of_finiteSearchFamily
    (F : FiniteSearchCertificate.RoleHingedFiniteSearchFamily) :
    targetUpperConstructionFiveSixteen :=
  matrix.finiteSearchFamily.exactTarget F

/-- Arbitrary target from a finite search family, routed through the split
exact-to-arbitrary bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_finiteSearchFamily
    (F : FiniteSearchCertificate.RoleHingedFiniteSearchFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.finiteSearchFamily.arbitraryTarget F

/-- Exact target from search-facing role-hinge transition facts and finite
data. -/
theorem targetUpperConstructionFiveSixteen_of_transitionFactsFiniteSearchFamily
    (F : RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily) :
    targetUpperConstructionFiveSixteen :=
  matrix.transitionFactsFiniteSearchFamily.exactTarget F

/-- Arbitrary target from search-facing role-hinge transition facts and finite
data. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionFactsFiniteSearchFamily
    (F : RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.transitionFactsFiniteSearchFamily.arbitraryTarget F

/-- Exact target from period-search data plus finite-index cross-block lower
bounds. -/
theorem targetUpperConstructionFiveSixteen_of_crossBlockLowerBounds
    (I : CrossBlockLowerBoundsInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.crossBlockLowerBounds.exactTarget I

/-- Arbitrary target from period-search data plus finite-index cross-block
lower bounds. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLowerBounds
    (I : CrossBlockLowerBoundsInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.crossBlockLowerBounds.arbitraryTarget I

/-- Exact target from a dependent cross-block lower-bound family. -/
theorem targetUpperConstructionFiveSixteen_of_crossBlockLowerBoundsFamily
    {F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F) :
    targetUpperConstructionFiveSixteen :=
  matrix.crossBlockLowerBounds.exactTarget
    { family := F
      lowerBounds := H }

/-- Arbitrary target from a dependent cross-block lower-bound family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLowerBoundsFamily
    {F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.crossBlockLowerBounds.arbitraryTarget
    { family := F
      lowerBounds := H }

/-- Exact target from an upper-triangle polynomial table family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTrianglePolynomialTables
    (I : UpperTrianglePolynomialTableInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.upperTrianglePolynomialTables.exactTarget I

/-- Arbitrary target from an upper-triangle polynomial table family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTrianglePolynomialTables
    (I : UpperTrianglePolynomialTableInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.upperTrianglePolynomialTables.arbitraryTarget I

/-- Exact target from a dependent upper-triangle polynomial table family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTrianglePolynomialTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTrianglePolynomialTableFamily F) :
    targetUpperConstructionFiveSixteen :=
  matrix.upperTrianglePolynomialTables.exactTarget
    { family := F
      tables := T }

/-- Arbitrary target from a dependent upper-triangle polynomial table family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTrianglePolynomialTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTrianglePolynomialTableFamily F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.upperTrianglePolynomialTables.arbitraryTarget
    { family := F
      tables := T }

/-- Exact target from an upper-triangle computed square-value table family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTriangleSqValueTables
    (I : UpperTriangleSqValueTableInput) :
    targetUpperConstructionFiveSixteen :=
  matrix.upperTriangleSqValueTables.exactTarget I

/-- Arbitrary target from an upper-triangle computed square-value table
family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleSqValueTables
    (I : UpperTriangleSqValueTableInput) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.upperTriangleSqValueTables.arbitraryTarget I

/-- Exact target from a dependent upper-triangle computed square-value table
family. -/
theorem targetUpperConstructionFiveSixteen_of_upperTriangleSqValueTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily F) :
    targetUpperConstructionFiveSixteen :=
  matrix.upperTriangleSqValueTables.exactTarget
    { family := F
      tables := T }

/-- Arbitrary target from a dependent upper-triangle computed square-value
table family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_upperTriangleSqValueTableFamily
    {F : CrossBlockSqTableSearch.RoleHingedPeriodSearchFamily}
    (T : CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.upperTriangleSqValueTables.arbitraryTarget
    { family := F
      tables := T }

/-- Exact target from concrete vector-backed upper-triangle tables. -/
theorem targetUpperConstructionFiveSixteen_of_vectorConcreteCrossBlock
    (C : CrossBlockUpperTriangleConcrete.VectorConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteen :=
  matrix.vectorConcreteCrossBlock.exactTarget C

/-- Arbitrary target from concrete vector-backed upper-triangle tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_vectorConcreteCrossBlock
    (C : CrossBlockUpperTriangleConcrete.VectorConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.vectorConcreteCrossBlock.arbitraryTarget C

/-- Exact target from concrete list-backed upper-triangle tables. -/
theorem targetUpperConstructionFiveSixteen_of_listConcreteCrossBlock
    (C : CrossBlockUpperTriangleConcrete.ListConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteen :=
  matrix.listConcreteCrossBlock.exactTarget C

/-- Arbitrary target from concrete list-backed upper-triangle tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_listConcreteCrossBlock
    (C : CrossBlockUpperTriangleConcrete.ListConcreteCrossBlockFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.listConcreteCrossBlock.arbitraryTarget C

end

end ExactFiveSixteenRouteMatrix
end PachToth
end ErdosProblems1066
