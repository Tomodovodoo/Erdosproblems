import ErdosProblems1066.Swanepoel.BrokenLatticeFieldsW11
import ErdosProblems1066.Swanepoel.SwanepoelTargetClosureW11
import ErdosProblems1066.Swanepoel.SwanepoelW10ClosureMatrix

set_option autoImplicit false

/-!
# W11 broken-lattice closure

This file is a target-facing closure layer for the W11 broken-lattice field
packages.  It proves only conditional routes: each public target theorem still
takes a uniform family of the required W11 fields as an explicit argument.

The strongest route exposed here is the common-neighbor geometry package.  It
forgets to the W10 common-neighbor geometry matrix, which already routes
through the K23 and W9 consumers to the Swanepoel target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeClosureW11

open MinimalGraphFacts

universe u

noncomputable section

abbrev Target : Prop :=
  SwanepoelTargetClosureW11.Target

abbrev MinimalFailureExclusion : Prop :=
  SwanepoelTargetClosureW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SwanepoelTargetClosureW11.PipelineCleared

/-! ## Fixed minimal-failure consumers -/

theorem contradiction_of_e22e23LocalPredicateFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (E : BrokenLatticeFieldsW11.E22E23LocalPredicateFields C hmin) :
    False :=
  E.contradiction

theorem contradiction_of_geometryE22E23PredicateFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (G : BrokenLatticeFieldsW11.GeometryE22E23PredicateFields.{u} C hmin) :
    False :=
  G.contradiction

theorem contradiction_of_directGeometryPredicateFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (D : BrokenLatticeFieldsW11.DirectGeometryPredicateFields.{u} C hmin) :
    False :=
  D.contradiction

theorem contradiction_of_k23GeometryPredicateFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (K : BrokenLatticeFieldsW11.K23GeometryPredicateFields.{u} C hmin) :
    False :=
  K.contradiction

theorem contradiction_of_commonNeighborGeometryPredicateFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BrokenLatticeFieldsW11.CommonNeighborGeometryPredicateFields.{u}
        C hmin) :
    False :=
  K.contradiction

/-! ## Uniform W11 field matrices -/

/-- Uniform analytic E22/E23 plus late-triples rows for every minimal failure. -/
structure E22E23LocalPredicateMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.E22E23LocalPredicateFields C hmin

namespace E22E23LocalPredicateMatrix

theorem no_minimalClearedFailure
    (M : E22E23LocalPredicateMatrix) :
    MinimalFailureExclusion := by
  intro n C hmin
  exact contradiction_of_e22e23LocalPredicateFields (M.row C hmin)

theorem pipelineCleared
    (M : E22E23LocalPredicateMatrix) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : E22E23LocalPredicateMatrix) :
    Target :=
  SwanepoelTargetFacadeW10.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

end E22E23LocalPredicateMatrix

/-- Uniform geometry-selected E22/E23 plus late-triples rows for every
minimal failure. -/
structure GeometryE22E23PredicateMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.GeometryE22E23PredicateFields.{u}
          C hmin

namespace GeometryE22E23PredicateMatrix

theorem no_minimalClearedFailure
    (M : GeometryE22E23PredicateMatrix.{u}) :
    MinimalFailureExclusion := by
  intro n C hmin
  exact contradiction_of_geometryE22E23PredicateFields (M.row C hmin)

theorem pipelineCleared
    (M : GeometryE22E23PredicateMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : GeometryE22E23PredicateMatrix.{u}) :
    Target :=
  SwanepoelTargetFacadeW10.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

end GeometryE22E23PredicateMatrix

/-- Uniform direct W11 geometry rows for every minimal failure. -/
structure DirectGeometryPredicateMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.DirectGeometryPredicateFields.{u}
          C hmin

namespace DirectGeometryPredicateMatrix

/-- Forget W11 direct geometry rows to the checked W10 direct geometry
matrix. -/
def toW10DirectGeometryMatrix
    (M : DirectGeometryPredicateMatrix.{u}) :
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPackage

theorem no_minimalClearedFailure
    (M : DirectGeometryPredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toW10DirectGeometryMatrix.no_minimalClearedFailure

theorem pipelineCleared
    (M : DirectGeometryPredicateMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : DirectGeometryPredicateMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    M.toW10DirectGeometryMatrix

end DirectGeometryPredicateMatrix

/-- Uniform K23-derived W11 geometry rows for every minimal failure. -/
structure K23GeometryPredicateMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.K23GeometryPredicateFields.{u}
          C hmin

namespace K23GeometryPredicateMatrix

/-- Forget W11 K23 geometry rows to the checked W10 K23 geometry matrix. -/
def toW10K23GeometryMatrix
    (M : K23GeometryPredicateMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPackage

theorem no_minimalClearedFailure
    (M : K23GeometryPredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toW10K23GeometryMatrix.no_minimalClearedFailure

theorem pipelineCleared
    (M : K23GeometryPredicateMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : K23GeometryPredicateMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    M.toW10K23GeometryMatrix

end K23GeometryPredicateMatrix

/-- Uniform common-neighbor-derived W11 geometry rows for every minimal
failure. -/
structure CommonNeighborGeometryPredicateMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BrokenLatticeFieldsW11.CommonNeighborGeometryPredicateFields.{u}
          C hmin

namespace CommonNeighborGeometryPredicateMatrix

/-- Forget W11 common-neighbor geometry rows to the checked W10
common-neighbor geometry matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborGeometryPackage

theorem no_minimalClearedFailure
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toW10CommonNeighborGeometryMatrix.no_minimalClearedFailure

theorem pipelineCleared
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    Target :=
  SwanepoelTargetClosureW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    M.toW10CommonNeighborGeometryMatrix

end CommonNeighborGeometryPredicateMatrix

/-! ## Checked route ledger -/

/-- Checked W11 broken-lattice route ledger.

The fields are projection functions only.  The ledger itself does not provide
any of the W11 input matrices. -/
structure Matrix : Type (u + 1) where
  w10ClosureMatrix : SwanepoelW10ClosureMatrix.Matrix.{u}
  e22e23LocalNoMinimal :
    E22E23LocalPredicateMatrix -> MinimalFailureExclusion
  e22e23LocalTarget :
    E22E23LocalPredicateMatrix -> Target
  geometryE22E23NoMinimal :
    GeometryE22E23PredicateMatrix.{u} -> MinimalFailureExclusion
  geometryE22E23Target :
    GeometryE22E23PredicateMatrix.{u} -> Target
  directGeometryNoMinimal :
    DirectGeometryPredicateMatrix.{u} -> MinimalFailureExclusion
  directGeometryTarget :
    DirectGeometryPredicateMatrix.{u} -> Target
  k23GeometryNoMinimal :
    K23GeometryPredicateMatrix.{u} -> MinimalFailureExclusion
  k23GeometryTarget :
    K23GeometryPredicateMatrix.{u} -> Target
  commonNeighborGeometryNoMinimal :
    CommonNeighborGeometryPredicateMatrix.{u} -> MinimalFailureExclusion
  commonNeighborGeometryTarget :
    CommonNeighborGeometryPredicateMatrix.{u} -> Target

/-- The checked W11 broken-lattice route ledger. -/
def matrix : Matrix.{u} where
  w10ClosureMatrix := SwanepoelW10ClosureMatrix.matrix
  e22e23LocalNoMinimal :=
    E22E23LocalPredicateMatrix.no_minimalClearedFailure
  e22e23LocalTarget :=
    E22E23LocalPredicateMatrix.targetLowerBoundEightThirtyOne
  geometryE22E23NoMinimal :=
    GeometryE22E23PredicateMatrix.no_minimalClearedFailure
  geometryE22E23Target :=
    GeometryE22E23PredicateMatrix.targetLowerBoundEightThirtyOne
  directGeometryNoMinimal :=
    DirectGeometryPredicateMatrix.no_minimalClearedFailure
  directGeometryTarget :=
    DirectGeometryPredicateMatrix.targetLowerBoundEightThirtyOne
  k23GeometryNoMinimal :=
    K23GeometryPredicateMatrix.no_minimalClearedFailure
  k23GeometryTarget :=
    K23GeometryPredicateMatrix.targetLowerBoundEightThirtyOne
  commonNeighborGeometryNoMinimal :=
    CommonNeighborGeometryPredicateMatrix.no_minimalClearedFailure
  commonNeighborGeometryTarget :=
    CommonNeighborGeometryPredicateMatrix.targetLowerBoundEightThirtyOne

/-! ## Public conditional projections -/

theorem no_minimalClearedFailure_of_e22e23LocalPredicateMatrix
    (M : E22E23LocalPredicateMatrix) :
    MinimalFailureExclusion :=
  E22E23LocalPredicateMatrix.no_minimalClearedFailure M

theorem targetLowerBoundEightThirtyOne_of_e22e23LocalPredicateMatrix
    (M : E22E23LocalPredicateMatrix) :
    Target :=
  E22E23LocalPredicateMatrix.targetLowerBoundEightThirtyOne M

theorem no_minimalClearedFailure_of_geometryE22E23PredicateMatrix
    (M : GeometryE22E23PredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.geometryE22E23NoMinimal M

theorem targetLowerBoundEightThirtyOne_of_geometryE22E23PredicateMatrix
    (M : GeometryE22E23PredicateMatrix.{u}) :
    Target :=
  matrix.geometryE22E23Target M

theorem no_minimalClearedFailure_of_directGeometryPredicateMatrix
    (M : DirectGeometryPredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.directGeometryNoMinimal M

theorem targetLowerBoundEightThirtyOne_of_directGeometryPredicateMatrix
    (M : DirectGeometryPredicateMatrix.{u}) :
    Target :=
  matrix.directGeometryTarget M

theorem no_minimalClearedFailure_of_k23GeometryPredicateMatrix
    (M : K23GeometryPredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.k23GeometryNoMinimal M

theorem targetLowerBoundEightThirtyOne_of_k23GeometryPredicateMatrix
    (M : K23GeometryPredicateMatrix.{u}) :
    Target :=
  matrix.k23GeometryTarget M

theorem no_minimalClearedFailure_of_commonNeighborGeometryPredicateMatrix
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborGeometryNoMinimal M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborGeometryPredicateMatrix
    (M : CommonNeighborGeometryPredicateMatrix.{u}) :
    Target :=
  matrix.commonNeighborGeometryTarget M

end

end BrokenLatticeClosureW11
end Swanepoel
end ErdosProblems1066
