import ErdosProblems1066.Swanepoel.M8LabelsFromBoundaryInterface

set_option autoImplicit false

/-!
# Concrete boundary-label package for `m = 8`

This file is a checked packaging layer on top of
`M8LabelsFromBoundaryInterface`.  It does not prove the missing boundary
spine or paper Lemma 8 combinatorics.  Instead, it records those explicit
inputs in one concrete package and projects them into the existing
`M8LocalLabels` and `M8ConstructionData` interfaces.

The remaining mathematical inputs are still visible as fields:
the boundary/cut/degree context, the boundary spine, the Lemma 8
extra-neighbor combinatorics, turn bounds, late triples, and window geometry.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8BoundaryLabelsConcrete

open GraphBridge
open Lemma10Bridge
open LocalConfigurations
open BrokenLatticePipeline
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

noncomputable section

/-! ## Boundary labels and Lemma 8 data -/

/-- Concrete boundary-derived label data.

The fields are deliberately the same honest inputs used by
`M8LabelsFromBoundaryInterface`: a boundary/cut/degree context, a spine of
labels `p_i, q_i`, and the explicit Lemma 8 combinatorics naming the extra
neighbors `r_i, s_i`. -/
structure M8BoundaryLabelPackage {n : Nat}
    (C : _root_.UDConfig n) where
  context : M8BoundaryCutDegreeContext C
  spine : M8BoundarySpine context
  lemma8 : M8Lemma8Combinatorics spine

namespace M8BoundaryLabelPackage

variable {n : Nat} {C : _root_.UDConfig n}

/-- Build the concrete package directly from a minimal cleared failure, an
outer boundary, a no-cut certificate, and explicit boundary/Lemma 8 labels. -/
def ofMinimalClearedFailure
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (spine :
      M8BoundarySpine
        (M8BoundaryCutDegreeContext.of_minimalClearedFailure
          outerBoundary connectedNoCut hmin))
    (lemma8 : M8Lemma8Combinatorics spine) :
    M8BoundaryLabelPackage C where
  context :=
    M8BoundaryCutDegreeContext.of_minimalClearedFailure
      outerBoundary connectedNoCut hmin
  spine := spine
  lemma8 := lemma8

/-- Build the concrete package from the connected/no-cut closure data. -/
def ofConnectedNoCutVertexClosureData
    (outerBoundary :
      OuterBoundaryCore
        (FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C))
    (H : CutVertexClosure.ConnectedNoCutVertexClosureData C)
    (spine :
      M8BoundarySpine
        (M8BoundaryCutDegreeContext.of_connectedNoCutVertexClosureData
          outerBoundary H))
    (lemma8 : M8Lemma8Combinatorics spine) :
    M8BoundaryLabelPackage C where
  context :=
    M8BoundaryCutDegreeContext.of_connectedNoCutVertexClosureData
      outerBoundary H
  spine := spine
  lemma8 := lemma8

/-- Forget the concrete wrapper to the interface package. -/
def toLabelsFromBoundaryData
    (D : M8BoundaryLabelPackage C) :
    M8LabelsFromBoundaryData C where
  context := D.context
  spine := D.spine
  lemma8 := D.lemma8

/-- The raw broken-lattice labels extracted from the boundary package. -/
def labels (D : M8BoundaryLabelPackage C) :
    BrokenLatticeLabels (Fin n) 8 :=
  D.toLabelsFromBoundaryData.labels

/-- The honest local predicate package extracted from the boundary package. -/
def predicates (D : M8BoundaryLabelPackage C) :
    M8HonestLocalPredicates (unitDistanceLocalGraph C) :=
  D.toLabelsFromBoundaryData.toHonestLocalPredicates

/-- The `M8LocalLabels` field extracted from boundary spine and Lemma 8 data.
-/
def toM8LocalLabels (D : M8BoundaryLabelPackage C) :
    M8LocalLabels C :=
  D.toLabelsFromBoundaryData.toM8LocalLabels

@[simp]
theorem toLabelsFromBoundaryData_context
    (D : M8BoundaryLabelPackage C) :
    D.toLabelsFromBoundaryData.context = D.context :=
  rfl

@[simp]
theorem toLabelsFromBoundaryData_spine
    (D : M8BoundaryLabelPackage C) :
    D.toLabelsFromBoundaryData.spine = D.spine :=
  rfl

@[simp]
theorem toLabelsFromBoundaryData_lemma8
    (D : M8BoundaryLabelPackage C) :
    D.toLabelsFromBoundaryData.lemma8 = D.lemma8 :=
  rfl

@[simp]
theorem labels_p (D : M8BoundaryLabelPackage C)
    (i : M8BoundaryIndex) :
    D.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem labels_q (D : M8BoundaryLabelPackage C)
    (i : M8TriangleIndex) :
    D.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem labels_r (D : M8BoundaryLabelPackage C)
    (i : M8ExtraIndex) :
    D.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem labels_s (D : M8BoundaryLabelPackage C)
    (i : M8ExtraIndex) :
    D.labels.s i = D.lemma8.s i :=
  rfl

@[simp]
theorem toM8LocalLabels_labels
    (D : M8BoundaryLabelPackage C) :
    D.toM8LocalLabels.labels = D.labels :=
  rfl

/-- Projection of a boundary-edge fact from the stored spine. -/
theorem boundaryEdge
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.predicates.data.boundaryEdge i :=
  D.spine.boundaryEdge i

/-- Projection of a triangle common-neighbor fact from the stored spine. -/
theorem triangleWitness
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.predicates.data.triangleWitness i :=
  D.spine.triangleWitness i

/-- Projection of the local extra-neighbor witness from the stored Lemma 8
package. -/
theorem extraNeighborWitness
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    D.predicates.data.extraNeighborWitness i :=
  D.lemma8.extraNeighborWitness_holds i

/-- Projection of the Lemma 8 exhaustiveness statement. -/
theorem named_of_extra_neighbor
    (D : M8BoundaryLabelPackage C)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (D.spine.centerQ i) x)
    (hnot : Not (D.spine.forbiddenExtraNeighbor i x)) :
    x = D.lemma8.r i \/ x = D.lemma8.s i :=
  D.lemma8.named_of_extra_neighbor hadj hnot

/-- Projection of the stored cyclic-order predicate from the Lemma 8 package.
-/
theorem positiveCyclicOrder
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    D.lemma8.positiveCyclicOrderAt i
      (D.lemma8.s i) (D.lemma8.r i)
      (D.spine.prevQ i) (D.spine.leftP i)
      (D.spine.rightP i) (D.spine.nextQ i) :=
  D.lemma8.positiveCyclicOrder_holds i

/-- Assemble the clean construction-interface package once the non-label M8
fields are supplied. -/
def toM8ConstructionData
    {hmin : IsMinimalClearedFailure C}
    (D : M8BoundaryLabelPackage C)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    M8ConstructionData C hmin :=
  D.toLabelsFromBoundaryData.toM8ConstructionData
    turnBounds lateTriples windowGeometry

@[simp]
theorem toM8ConstructionData_localLabels
    {hmin : IsMinimalClearedFailure C}
    (D : M8BoundaryLabelPackage C)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData (hmin := hmin)
      turnBounds lateTriples windowGeometry).localLabels =
        D.toM8LocalLabels :=
  rfl

@[simp]
theorem toM8ConstructionData_turnBounds
    {hmin : IsMinimalClearedFailure C}
    (D : M8BoundaryLabelPackage C)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData (hmin := hmin)
      turnBounds lateTriples windowGeometry).turnBounds =
        turnBounds :=
  rfl

end M8BoundaryLabelPackage

/-! ## Full construction package -/

/-- Boundary labels plus the remaining explicit construction fields for one
minimal cleared failure. -/
structure M8BoundaryConstructionPackage {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundaryLabels : M8BoundaryLabelPackage C
  turnBounds : M8TurnBounds
  lateTriples : M8LateTriples boundaryLabels.toM8LocalLabels
  windowGeometry :
    M8WindowGeometry boundaryLabels.toM8LocalLabels turnBounds

namespace M8BoundaryConstructionPackage

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Projection to the local-label field. -/
def localLabels
    (D : M8BoundaryConstructionPackage C hmin) :
    M8LocalLabels C :=
  D.boundaryLabels.toM8LocalLabels

/-- Projection to the honest local predicates. -/
def predicates
    (D : M8BoundaryConstructionPackage C hmin) :
    M8HonestLocalPredicates (unitDistanceLocalGraph C) :=
  D.localLabels.predicates

/-- Forget the concrete boundary package to the clean construction interface.
-/
def toM8ConstructionData
    (D : M8BoundaryConstructionPackage C hmin) :
    M8ConstructionData C hmin :=
  D.boundaryLabels.toM8ConstructionData
    D.turnBounds D.lateTriples D.windowGeometry

/-- Compose with the existing broken-lattice minimal-failure interface. -/
def toBrokenLatticeMinimalFailure
    (D : M8BoundaryConstructionPackage C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  D.toM8ConstructionData.toBrokenLatticeMinimalFailure

@[simp]
theorem toM8ConstructionData_localLabels
    (D : M8BoundaryConstructionPackage C hmin) :
    D.toM8ConstructionData.localLabels = D.localLabels :=
  rfl

@[simp]
theorem toM8ConstructionData_turnBounds
    (D : M8BoundaryConstructionPackage C hmin) :
    D.toM8ConstructionData.turnBounds = D.turnBounds :=
  rfl

/-- The assembled package contradicts the indexed minimal cleared failure via
the already checked broken-lattice closure. -/
theorem contradiction
    (D : M8BoundaryConstructionPackage C hmin) :
    False :=
  D.toBrokenLatticeMinimalFailure.contradiction

end M8BoundaryConstructionPackage

end

end M8BoundaryLabelsConcrete
end Swanepoel
end ErdosProblems1066
