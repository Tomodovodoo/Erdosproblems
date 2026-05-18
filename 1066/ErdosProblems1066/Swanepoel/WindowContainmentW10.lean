import ErdosProblems1066.Swanepoel.M8WindowContainmentConcrete
import ErdosProblems1066.Swanepoel.OuterBoundaryLabelFacts
import ErdosProblems1066.Swanepoel.SwanepoelRemainingObligationsW9

set_option autoImplicit false

/-!
# W10 window-containment bridge

This module is a thin W10 facade from boundary-derived labels and explicit
Figure 8/Figure 9 angle containment to the M8 window-containment packages used
by the W9 rows.

No geometric estimate is added here.  The only inputs are the selected
angle-containment records, and the only outputs are exact package fields,
selected witnesses, and E22/E23 projections already supplied by the M8
containment interfaces.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace WindowContainmentW10

open AngleBridgeFacts
open AngleContainmentInterface
open AngleGeometry
open GraphBridge
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts
open SwanepoelRemainingObligationsW9

universe u

/-! ## Local angle-containment fields -/

/-- Exact angle-containment input for fixed local labels and turn bounds. -/
structure LocalAngleContainmentFields {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  angleContainment :
    AngleContainmentBridges
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn

namespace LocalAngleContainmentFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- The exact Figure 8 containment field. -/
def figure8ContainmentInterface
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  H.angleContainment.figure8

/-- The exact Figure 9 adjacent-left containment field. -/
def figure9LeftContainmentInterface
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  H.angleContainment.figure9

/-- Package the angle-containment input as concrete M8 local window fields. -/
def windowFields
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    M8LocalWindowContainmentFields localLabels turnBounds :=
  M8LocalWindowContainmentFields.ofAngleContainmentBridges
    H.angleContainment

/-- Package the angle-containment input as the construction window record. -/
def windowContainment
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    M8WindowContainment localLabels turnBounds :=
  H.windowFields.toM8WindowContainment

/-- The same data as the generic angle-containment bridge. -/
def toAngleContainmentBridges
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    AngleContainmentBridges
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  H.angleContainment

@[simp]
theorem windowFields_figure8
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    H.windowFields.figure8 = H.angleContainment.figure8 :=
  rfl

@[simp]
theorem windowFields_figure9_left
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    H.windowFields.figure9_left = H.angleContainment.figure9 :=
  rfl

@[simp]
theorem windowContainment_figure8
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    H.windowContainment.figure8 = H.angleContainment.figure8 :=
  rfl

@[simp]
theorem windowContainment_figure9_left
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    H.windowContainment.figure9_left = H.angleContainment.figure9 :=
  rfl

/-- Figure 8 selected witness for a separated failed pair. -/
def figure8ExtractedData
    (H : LocalAngleContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Figure8SeparatedExtractedData :=
  H.windowFields.figure8ExtractedData hi hsep hj hbad_i hbad_j

/-- Figure 8 selected witness with its central-angle containment. -/
def figure8ContainedData
    (H : LocalAngleContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Figure8SeparatedContainedData turnBounds.turn i j :=
  H.windowFields.figure8ContainedData hi hsep hj hbad_i hbad_j

/-- Figure 8 central-angle containment for any matching distance package. -/
theorem figure8_central_angle_le_separatedTurn
    (H : LocalAngleContainmentFields localLabels turnBounds)
    {i j : Nat} {p qi qj s r : AngleGeometry.Point}
    (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j))
    (D : Figure8DistanceData p qi qj s r) :
    angleAt qi p qj <= separatedTurn turnBounds.turn i j :=
  H.windowFields.figure8_central_angle_le_separatedTurn
    hi hsep hj hbad_i hbad_j D

/-- Figure 9 selected witness for an adjacent failed pair. -/
def figure9LeftExtractedData
    (H : LocalAngleContainmentFields localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1))) :
    Figure9AdjacentExtractedData :=
  H.windowFields.figure9LeftExtractedData
    hi hi_next hbad_i hbad_next

/-- Figure 9 selected witness with its left-angle containment. -/
def figure9LeftContainedData
    (H : LocalAngleContainmentFields localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1))) :
    Figure9AdjacentLeftContainedData turnBounds.turn i :=
  H.windowFields.figure9LeftContainedData
    hi hi_next hbad_i hbad_next

/-- Figure 9 left-angle containment for any matching distance package. -/
theorem figure9_left_angle_le_adjacentTurn
    (H : LocalAngleContainmentFields localLabels turnBounds)
    {i : Nat} {p qi qj s r : AngleGeometry.Point}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1)))
    (D : Figure9DistanceData p qi qj s r) :
    angleAt p qi s <= adjacentTurn turnBounds.turn i :=
  H.windowFields.figure9_left_angle_le_adjacentTurn
    hi hi_next hbad_i hbad_next D

/-- Conditional E22 projection from the supplied Figure 8 containment. -/
theorem figure8_E22
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  H.windowFields.figure8_E22

/-- Conditional E23 projection from the supplied Figure 9 containment. -/
theorem figure9_E23
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  H.windowFields.figure9_E23

/-- Paired conditional E22/E23 projection. -/
theorem E22_E23
    (H : LocalAngleContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  H.windowFields.E22_E23

/-- Pointwise E22 projection for a separated failed pair. -/
theorem figure8_E22_apply
    (H : LocalAngleContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Real.pi / 3 <= separatedTurn turnBounds.turn i j :=
  H.windowFields.figure8_E22_apply hi hsep hj hbad_i hbad_j

/-- Pointwise E23 projection for an adjacent failed pair. -/
theorem figure9_E23_apply
    (H : LocalAngleContainmentFields localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1))) :
    Real.pi / 3 <= adjacentTurn turnBounds.turn i :=
  H.windowFields.figure9_E23_apply hi hi_next hbad_i hbad_next

end LocalAngleContainmentFields

/-! ## Boundary-derived labels -/

/-- Angle-containment input specialized to labels extracted from boundary data. -/
abbrev LabelsFromBoundaryAngleContainmentFields
    {n : Nat} {C : _root_.UDConfig n}
    (D : M8LabelsFromBoundaryData C) (turnBounds : M8TurnBounds) :
    Type :=
  LocalAngleContainmentFields D.toM8LocalLabels turnBounds

namespace LabelsFromBoundaryAngleContainmentFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {D : M8LabelsFromBoundaryData C}
variable {turnBounds : M8TurnBounds}

/-- Build the boundary-label window facade from a combined angle bridge. -/
def ofAngleContainmentBridges
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
        turnBounds.turn) :
    LabelsFromBoundaryAngleContainmentFields D turnBounds where
  angleContainment := A

/-- Boundary-derived angle data as concrete local window fields. -/
def windowFields
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds) :
    M8LabelsFromBoundaryWindowContainmentFields D turnBounds :=
  LocalAngleContainmentFields.windowFields H

/-- Boundary-derived angle data as the M8 window-containment record. -/
def windowContainment
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds) :
    M8WindowContainment D.toM8LocalLabels turnBounds :=
  LocalAngleContainmentFields.windowContainment H

/-- The exact Figure 8 containment field. -/
def figure8ContainmentInterface
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds) :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  LocalAngleContainmentFields.figure8ContainmentInterface H

/-- The exact Figure 9 adjacent-left containment field. -/
def figure9LeftContainmentInterface
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds) :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  LocalAngleContainmentFields.figure9LeftContainmentInterface H

@[simp]
theorem localLabels_p
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8BoundaryIndex) :
    D.toM8LocalLabels.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem localLabels_q
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8TriangleIndex) :
    D.toM8LocalLabels.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem localLabels_r
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem localLabels_s
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.s i = D.lemma8.s i :=
  rfl

/-- Boundary location of the selected `p` label. -/
theorem p_onOuterBoundary
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8BoundaryIndex) :
    D.context.outerBoundary.outerEnclosure.onBoundary
      (D.toM8LocalLabels.labels.p i) := by
  simpa using OuterBoundaryLabelFacts.M8LabelsFromBoundaryData.p_onOuterBoundary
    D i

/-- Boundary-edge predicate carried by the selected labels. -/
theorem boundaryEdge
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8TriangleIndex) :
    D.toM8LocalLabels.predicates.data.boundaryEdge i := by
  simpa using OuterBoundaryLabelFacts.M8LabelsFromBoundaryData.boundaryEdge
    D i

/-- Triangle-witness predicate carried by the selected labels. -/
theorem triangleWitness
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8TriangleIndex) :
    D.toM8LocalLabels.predicates.data.triangleWitness i := by
  simpa using OuterBoundaryLabelFacts.M8LabelsFromBoundaryData.triangleWitness
    D i

/-- Extra-neighbor predicate carried by the selected labels. -/
theorem extraNeighborWitness
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.predicates.data.extraNeighborWitness i := by
  simpa using
    OuterBoundaryLabelFacts.M8LabelsFromBoundaryData.extraNeighborWitness D i

/-- Raw adjacency of the selected `r` extra neighbor. -/
theorem extra_r_neighbor
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.toM8LocalLabels.labels.r i) := by
  simpa using
    OuterBoundaryLabelFacts.M8LabelsFromBoundaryData.extra_r_neighbor D i

/-- Raw adjacency of the selected `s` extra neighbor. -/
theorem extra_s_neighbor
    (_H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.toM8LocalLabels.labels.s i) := by
  simpa using
    OuterBoundaryLabelFacts.M8LabelsFromBoundaryData.extra_s_neighbor D i

/-- Figure 8 selected witness for boundary-derived labels. -/
def figure8ExtractedData
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data j)) :
    Figure8SeparatedExtractedData :=
  LocalAngleContainmentFields.figure8ExtractedData
    H hi hsep hj hbad_i hbad_j

/-- Figure 8 selected witness with its central-angle containment. -/
def figure8ContainedData
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data j)) :
    Figure8SeparatedContainedData turnBounds.turn i j :=
  LocalAngleContainmentFields.figure8ContainedData
    H hi hsep hj hbad_i hbad_j

/-- Figure 9 selected witness for boundary-derived labels. -/
def figure9LeftExtractedData
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood
        D.toM8LocalLabels.predicates.data (i + 1))) :
    Figure9AdjacentExtractedData :=
  LocalAngleContainmentFields.figure9LeftExtractedData
    H hi hi_next hbad_i hbad_next

/-- Figure 9 selected witness with its left-angle containment. -/
def figure9LeftContainedData
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood
        D.toM8LocalLabels.predicates.data (i + 1))) :
    Figure9AdjacentLeftContainedData turnBounds.turn i :=
  LocalAngleContainmentFields.figure9LeftContainedData
    H hi hi_next hbad_i hbad_next

/-- Conditional E22 projection for boundary-derived labels. -/
theorem figure8_E22
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      D.toM8LocalLabels.predicates turnBounds.turn :=
  LocalAngleContainmentFields.figure8_E22 H

/-- Conditional E23 projection for boundary-derived labels. -/
theorem figure9_E23
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      D.toM8LocalLabels.predicates turnBounds.turn :=
  LocalAngleContainmentFields.figure9_E23 H

/-- Paired conditional E22/E23 projection for boundary-derived labels. -/
theorem E22_E23
    (H : LabelsFromBoundaryAngleContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        D.toM8LocalLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        D.toM8LocalLabels.predicates turnBounds.turn :=
  LocalAngleContainmentFields.E22_E23 H

end LabelsFromBoundaryAngleContainmentFields

/-! ## Boundary-label package specialization -/

/-- Angle-containment input specialized to the concrete boundary-label package. -/
abbrev BoundaryPackageAngleContainmentFields
    {n : Nat} {C : _root_.UDConfig n}
    (D : M8BoundaryLabelPackage C) (turnBounds : M8TurnBounds) :
    Type :=
  LocalAngleContainmentFields D.toM8LocalLabels turnBounds

namespace BoundaryPackageAngleContainmentFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {D : M8BoundaryLabelPackage C}
variable {turnBounds : M8TurnBounds}

/-- Build the boundary-package window facade from a combined angle bridge. -/
def ofAngleContainmentBridges
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
        turnBounds.turn) :
    BoundaryPackageAngleContainmentFields D turnBounds where
  angleContainment := A

/-- Boundary-package angle data as boundary-derived label data. -/
def toLabelsFromBoundaryFields
    (H : BoundaryPackageAngleContainmentFields D turnBounds) :
    LabelsFromBoundaryAngleContainmentFields
      D.toLabelsFromBoundaryData turnBounds :=
  H

/-- Boundary-package angle data as concrete local window fields. -/
def windowFields
    (H : BoundaryPackageAngleContainmentFields D turnBounds) :
    M8BoundaryLabelPackageWindowContainmentFields D turnBounds :=
  LocalAngleContainmentFields.windowFields H

/-- Boundary-package angle data as the M8 window-containment record. -/
def windowContainment
    (H : BoundaryPackageAngleContainmentFields D turnBounds) :
    M8WindowContainment D.toM8LocalLabels turnBounds :=
  LocalAngleContainmentFields.windowContainment H

@[simp]
theorem localLabels_p
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8BoundaryIndex) :
    D.toM8LocalLabels.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem localLabels_q
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8TriangleIndex) :
    D.toM8LocalLabels.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem localLabels_r
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem localLabels_s
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.s i = D.lemma8.s i :=
  rfl

/-- Boundary location of the selected `p` label. -/
theorem p_onOuterBoundary
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8BoundaryIndex) :
    D.context.outerBoundary.outerEnclosure.onBoundary
      (D.toM8LocalLabels.labels.p i) := by
  simpa using OuterBoundaryLabelFacts.M8BoundaryLabelPackage.p_onOuterBoundary
    D i

/-- Boundary-edge predicate carried by the selected package. -/
theorem boundaryEdge
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8TriangleIndex) :
    D.toM8LocalLabels.predicates.data.boundaryEdge i := by
  simpa using OuterBoundaryLabelFacts.M8BoundaryLabelPackage.boundaryEdge D i

/-- Triangle-witness predicate carried by the selected package. -/
theorem triangleWitness
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8TriangleIndex) :
    D.toM8LocalLabels.predicates.data.triangleWitness i := by
  simpa using OuterBoundaryLabelFacts.M8BoundaryLabelPackage.triangleWitness
    D i

/-- Extra-neighbor predicate carried by the selected package. -/
theorem extraNeighborWitness
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.predicates.data.extraNeighborWitness i := by
  simpa using
    OuterBoundaryLabelFacts.M8BoundaryLabelPackage.extraNeighborWitness D i

/-- Raw adjacency of the selected `r` extra neighbor. -/
theorem extra_r_neighbor
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.toM8LocalLabels.labels.r i) := by
  simpa using OuterBoundaryLabelFacts.M8BoundaryLabelPackage.extra_r_neighbor
    D i

/-- Raw adjacency of the selected `s` extra neighbor. -/
theorem extra_s_neighbor
    (_H : BoundaryPackageAngleContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) (D.toM8LocalLabels.labels.s i) := by
  simpa using OuterBoundaryLabelFacts.M8BoundaryLabelPackage.extra_s_neighbor
    D i

/-- Conditional E22 projection for the boundary-label package. -/
theorem figure8_E22
    (H : BoundaryPackageAngleContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      D.toM8LocalLabels.predicates turnBounds.turn :=
  LocalAngleContainmentFields.figure8_E22 H

/-- Conditional E23 projection for the boundary-label package. -/
theorem figure9_E23
    (H : BoundaryPackageAngleContainmentFields D turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      D.toM8LocalLabels.predicates turnBounds.turn :=
  LocalAngleContainmentFields.figure9_E23 H

/-- Paired conditional E22/E23 projection for the boundary-label package. -/
theorem E22_E23
    (H : BoundaryPackageAngleContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        D.toM8LocalLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        D.toM8LocalLabels.predicates turnBounds.turn :=
  LocalAngleContainmentFields.E22_E23 H

end BoundaryPackageAngleContainmentFields

/-! ## W9 base-row bridge -/

/-- W10 angle-containment row for the exact labels and turns selected by a W9
base row. -/
structure W9BaseAngleContainmentRow
    {n : Nat} (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (base : BaseRow.{u} C hmin) where
  angleContainment :
    AngleContainmentBridges
      (M8BrokenLatticeGood base.localLabels.predicates.data)
      base.turnBounds.turn

namespace W9BaseAngleContainmentRow

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}
variable {base : BaseRow.{u} C hmin}

/-- The W9 base-row angle data as local window fields. -/
def localFields
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    LocalAngleContainmentFields base.localLabels base.turnBounds where
  angleContainment := H.angleContainment

/-- The W9 base-row angle data as boundary-derived label fields. -/
def labelsFromBoundaryFields
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    LabelsFromBoundaryAngleContainmentFields base.labels base.turnBounds where
  angleContainment := H.angleContainment

/-- The W9 base-row angle data as concrete M8 local window fields. -/
def windowFields
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    M8LocalWindowContainmentFields base.localLabels base.turnBounds :=
  H.localFields.windowFields

/-- The W9 base-row angle data as the M8 window-containment record. -/
def windowContainment
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    M8WindowContainment base.localLabels base.turnBounds :=
  H.localFields.windowContainment

/-- The W9 window row obtained from angle containment. -/
def toWindowRow
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    WindowRow.{u} C hmin base where
  containment := H.windowContainment

@[simp]
theorem toWindowRow_containment
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    H.toWindowRow.containment = H.windowContainment :=
  rfl

/-- The exact Figure 8 containment field in the induced W9 window row. -/
theorem toWindowRow_figure8
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    H.toWindowRow.containment.figure8 = H.angleContainment.figure8 :=
  rfl

/-- The exact Figure 9 adjacent-left containment field in the induced W9
window row. -/
theorem toWindowRow_figure9_left
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    H.toWindowRow.containment.figure9_left = H.angleContainment.figure9 :=
  rfl

/-- Figure 8 selected witness for the W9 base-row labels. -/
def figure8ExtractedData
    (H : W9BaseAngleContainmentRow.{u} C hmin base)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood base.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood base.localLabels.predicates.data j)) :
    Figure8SeparatedExtractedData :=
  H.localFields.figure8ExtractedData hi hsep hj hbad_i hbad_j

/-- Figure 8 selected witness with central-angle containment for the W9
base-row labels. -/
def figure8ContainedData
    (H : W9BaseAngleContainmentRow.{u} C hmin base)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood base.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood base.localLabels.predicates.data j)) :
    Figure8SeparatedContainedData base.turnBounds.turn i j :=
  H.localFields.figure8ContainedData hi hsep hj hbad_i hbad_j

/-- Figure 9 selected witness for the W9 base-row labels. -/
def figure9LeftExtractedData
    (H : W9BaseAngleContainmentRow.{u} C hmin base)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood base.localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood base.localLabels.predicates.data (i + 1))) :
    Figure9AdjacentExtractedData :=
  H.localFields.figure9LeftExtractedData hi hi_next hbad_i hbad_next

/-- Figure 9 selected witness with left-angle containment for the W9 base-row
labels. -/
def figure9LeftContainedData
    (H : W9BaseAngleContainmentRow.{u} C hmin base)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood base.localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood base.localLabels.predicates.data (i + 1))) :
    Figure9AdjacentLeftContainedData base.turnBounds.turn i :=
  H.localFields.figure9LeftContainedData hi hi_next hbad_i hbad_next

/-- Conditional E22 projection for the W9 base row. -/
theorem figure8_E22
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    HonestFigure8SeparatedWindowLowerE22
      base.localLabels.predicates base.turnBounds.turn :=
  H.localFields.figure8_E22

/-- Conditional E23 projection for the W9 base row. -/
theorem figure9_E23
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    HonestFigure9AdjacentWindowLowerE23
      base.localLabels.predicates base.turnBounds.turn :=
  H.localFields.figure9_E23

/-- Paired conditional E22/E23 projection for the W9 base row. -/
theorem E22_E23
    (H : W9BaseAngleContainmentRow.{u} C hmin base) :
    HonestFigure8SeparatedWindowLowerE22
        base.localLabels.predicates base.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        base.localLabels.predicates base.turnBounds.turn :=
  H.localFields.E22_E23

end W9BaseAngleContainmentRow

end WindowContainmentW10
end Swanepoel
end ErdosProblems1066

end
