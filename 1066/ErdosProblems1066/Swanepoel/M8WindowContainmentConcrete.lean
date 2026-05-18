import ErdosProblems1066.Swanepoel.BoundaryLabelExtractionTasks
import ErdosProblems1066.Swanepoel.Figure8ContainmentConcrete
import ErdosProblems1066.Swanepoel.Figure9ContainmentConcrete
import ErdosProblems1066.Swanepoel.M8WindowGeometryFromContainment

set_option autoImplicit false

/-!
# Concrete M8 window-containment fields

This file packages the exact Figure 8/Figure 9 local containment hypotheses
needed to fill the `M8WindowContainment` fields used by the refined M8 and
minimal-failure rows.

No geometric estimate is introduced here.  The Figure 8 and Figure 9
hypotheses are the containment interfaces already checked in
`Figure8ContainmentConcrete` and `Figure9ContainmentConcrete`; this file only
specializes them to the local-label packages produced by the boundary-label
route and projects them to the named E22/E23 hypotheses.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace M8WindowContainmentConcrete

open AngleContainmentInterface
open AngleBridgeFacts
open AngleGeometry
open BoundaryLabelExtractionTasks
open Figure8ContainmentConcrete
open Figure9ContainmentConcrete
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

/-! ## Local-label window containment -/

/-- The two concrete containment fields needed to build
`M8WindowContainment` for a fixed local-label package and turn budget. -/
structure M8LocalWindowContainmentFields {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  figure8 :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn
  figure9_left :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn

namespace M8LocalWindowContainmentFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- Package separately supplied exact Figure 8 and Figure 9 containment
interfaces as the local window-containment fields. -/
def ofContainmentInterfaces
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    M8LocalWindowContainmentFields localLabels turnBounds where
  figure8 := figure8
  figure9_left := figure9_left

/-- Package a combined angle-containment bridge as local
window-containment fields. -/
def ofAngleContainmentBridges
    (H :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    M8LocalWindowContainmentFields localLabels turnBounds :=
  ofContainmentInterfaces H.figure8 H.figure9

/-- Package the local Figure 8/Figure 9 containment fields as the construction
window-containment record consumed downstream. -/
def toM8WindowContainment
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    M8WindowContainment localLabels turnBounds where
  figure8 := H.figure8
  figure9_left := H.figure9_left

/-- The exact Figure 8 containment interface carried by the local fields. -/
def figure8ContainmentInterface
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  H.figure8

/-- The exact Figure 9 adjacent-left containment interface carried by the
local fields. -/
def figure9LeftContainmentInterface
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  H.figure9_left

@[simp]
theorem ofContainmentInterfaces_figure8
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    (ofContainmentInterfaces
      (localLabels := localLabels) (turnBounds := turnBounds)
      figure8 figure9_left).figure8 = figure8 :=
  rfl

@[simp]
theorem ofContainmentInterfaces_figure9_left
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    (ofContainmentInterfaces
      (localLabels := localLabels) (turnBounds := turnBounds)
      figure8 figure9_left).figure9_left = figure9_left :=
  rfl

@[simp]
theorem ofAngleContainmentBridges_figure8
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    (ofAngleContainmentBridges
      (localLabels := localLabels) (turnBounds := turnBounds) A).figure8 =
      A.figure8 :=
  rfl

@[simp]
theorem ofAngleContainmentBridges_figure9_left
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    (ofAngleContainmentBridges
      (localLabels := localLabels) (turnBounds := turnBounds) A).figure9_left =
      A.figure9 :=
  rfl

@[simp]
theorem toM8WindowContainment_figure8
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    H.toM8WindowContainment.figure8 = H.figure8 :=
  rfl

@[simp]
theorem toM8WindowContainment_figure9_left
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    H.toM8WindowContainment.figure9_left = H.figure9_left :=
  rfl

/-- The same fields as a combined angle-containment bridge. -/
def toAngleContainmentBridges
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    AngleContainmentBridges
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  H.toM8WindowContainment.toAngleContainmentBridges

/-- The same fields as construction-interface window geometry. -/
def toM8WindowGeometry
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    M8WindowGeometry localLabels turnBounds :=
  H.toM8WindowContainment.toM8WindowGeometry

/-- Figure 8 window-geometry projection from the explicit fields. -/
def figure8WindowGeometry
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowGeometry
      localLabels.predicates turnBounds.turn :=
  H.toM8WindowGeometry.figure8

/-- Figure 9 adjacent-left window-geometry projection from the explicit
fields. -/
def figure9LeftWindowGeometry
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure9AdjacentLeftWindowGeometry
      localLabels.predicates turnBounds.turn :=
  H.toM8WindowGeometry.figure9_left

/-- Figure 8 selected-window containment obtained from the local fields. -/
def figure8WindowContainment
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowContainment
      localLabels.predicates turnBounds.turn :=
  Figure8SeparatedWindowContainment.ofContainmentInterface H.figure8

/-- Figure 9 selected adjacent-left containment obtained from the local
fields. -/
def figure9LeftWindowContainment
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure9AdjacentLeftWindowContainment
      localLabels.predicates turnBounds.turn :=
  Figure9AdjacentLeftWindowContainment.ofContainmentInterface H.figure9_left

/-- Projection of the Figure 8 containment field to the honest E22 lower
bound. -/
theorem figure8_E22
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  (H.figure8WindowContainment).E22

/-- Projection of the Figure 9 containment field to the honest E23 lower
bound. -/
theorem figure9_E23
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  (H.figure9LeftWindowContainment).E23

/-- Paired E22/E23 lower-bound projection from the concrete local fields. -/
theorem E22_E23
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  And.intro H.figure8_E22 H.figure9_E23

/-- The local fields agree with the existing containment-to-E22/E23 route. -/
theorem E22_E23_via_m8WindowContainment
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  H.toM8WindowContainment.E22_E23

/-- The construction-interface window-geometry field gives the honest E22
projection from the explicit Figure 8 field. -/
theorem figure8_E22_via_m8WindowGeometry
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  H.toM8WindowGeometry.figure8_E22

/-- The construction-interface window-geometry field gives the honest E23
projection from the explicit Figure 9 field. -/
theorem figure9_E23_via_m8WindowGeometry
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  H.toM8WindowGeometry.figure9_E23

/-- Paired E22/E23 projections through the construction-interface
window-geometry field. -/
theorem E22_E23_via_m8WindowGeometry
    (H : M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  And.intro H.figure8_E22_via_m8WindowGeometry
    H.figure9_E23_via_m8WindowGeometry

/-- The selected Figure 8 extracted data exposed from the explicit fields. -/
def figure8ExtractedData
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Figure8SeparatedExtractedData :=
  H.figure8.extractedData hi hsep hj hbad_i hbad_j

/-- The selected Figure 8 contained data exposed from the explicit fields. -/
def figure8ContainedData
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Figure8SeparatedContainedData turnBounds.turn i j :=
  H.figure8.containedData hi hsep hj hbad_i hbad_j

/-- The exact Figure 8 central-angle containment exposed from the explicit
fields. -/
theorem figure8_central_angle_le_separatedTurn
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i j : Nat} {p qi qj s r : AngleGeometry.Point}
    (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j))
    (D : Figure8DistanceData p qi qj s r) :
    angleAt qi p qj <= separatedTurn turnBounds.turn i j :=
  H.figure8.central_angle_le_separatedTurn
    hi hsep hj hbad_i hbad_j D

/-- The selected Figure 9 extracted data exposed from the explicit fields. -/
def figure9LeftExtractedData
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1))) :
    Figure9AdjacentExtractedData :=
  H.figure9_left.extractedData hi hi_next hbad_i hbad_next

/-- The selected Figure 9 contained data exposed from the explicit fields. -/
def figure9LeftContainedData
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1))) :
    Figure9AdjacentLeftContainedData turnBounds.turn i :=
  H.figure9_left.containedData hi hi_next hbad_i hbad_next

/-- The exact Figure 9 left-angle containment exposed from the explicit
fields. -/
theorem figure9_left_angle_le_adjacentTurn
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i : Nat} {p qi qj s r : AngleGeometry.Point}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1)))
    (D : Figure9DistanceData p qi qj s r) :
    angleAt p qi s <= adjacentTurn turnBounds.turn i :=
  H.figure9_left.left_angle_le_adjacentTurn
    hi hi_next hbad_i hbad_next D

/-- Pointwise Figure 8/E22 projection for a separated failed pair. -/
theorem figure8_E22_apply
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Real.pi / 3 <= separatedTurn turnBounds.turn i j :=
  H.figure8_E22 hi hsep hj hbad_i hbad_j

/-- Pointwise Figure 9/E23 projection for an adjacent failed pair. -/
theorem figure9_E23_apply
    (H : M8LocalWindowContainmentFields localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1))) :
    Real.pi / 3 <= adjacentTurn turnBounds.turn i :=
  H.figure9_E23 hi hi_next hbad_i hbad_next

end M8LocalWindowContainmentFields

/-! ## Boundary-extracted label specializations -/

/-- Concrete window-containment fields specialized to labels extracted from
`M8LabelsFromBoundaryData`.  This is the exact window field shape used by the
minimal-failure row whose labels are stored as boundary-extraction data. -/
abbrev M8LabelsFromBoundaryWindowContainmentFields
    {n : Nat} {C : _root_.UDConfig n}
    (D : M8LabelsFromBoundaryData C) (turnBounds : M8TurnBounds) :
    Type :=
  M8LocalWindowContainmentFields D.toM8LocalLabels turnBounds

namespace M8LabelsFromBoundaryWindowContainmentFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {D : M8LabelsFromBoundaryData C}
variable {turnBounds : M8TurnBounds}

/-- Boundary-extracted labels with separately supplied exact Figure 8 and
Figure 9 containment interfaces. -/
def ofContainmentInterfaces
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
        turnBounds.turn) :
    M8LabelsFromBoundaryWindowContainmentFields D turnBounds :=
  M8LocalWindowContainmentFields.ofContainmentInterfaces
    (localLabels := D.toM8LocalLabels) (turnBounds := turnBounds)
    figure8 figure9_left

/-- Boundary-extracted labels with a combined angle-containment bridge. -/
def ofAngleContainmentBridges
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
        turnBounds.turn) :
    M8LabelsFromBoundaryWindowContainmentFields D turnBounds :=
  M8LocalWindowContainmentFields.ofAngleContainmentBridges
    (localLabels := D.toM8LocalLabels) (turnBounds := turnBounds) A

/-- Boundary-extracted fields packaged as `M8WindowContainment`. -/
def toM8WindowContainment
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    M8WindowContainment D.toM8LocalLabels turnBounds :=
  M8LocalWindowContainmentFields.toM8WindowContainment H

/-- The exact Figure 8 containment field for boundary-extracted labels. -/
def figure8ContainmentInterface
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  M8LocalWindowContainmentFields.figure8ContainmentInterface H

/-- The exact Figure 9 adjacent-left containment field for boundary-extracted
labels. -/
def figure9LeftContainmentInterface
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  M8LocalWindowContainmentFields.figure9LeftContainmentInterface H

/-- Boundary-extracted fields repackaged as the combined angle-containment
bridge. -/
def toAngleContainmentBridges
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    AngleContainmentBridges
      (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  M8LocalWindowContainmentFields.toAngleContainmentBridges H

/-- Boundary-extracted fields packaged as construction-interface window
geometry. -/
def toM8WindowGeometry
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    M8WindowGeometry D.toM8LocalLabels turnBounds :=
  M8LocalWindowContainmentFields.toM8WindowGeometry H

/-- Figure 8 window geometry from the boundary-extracted explicit fields. -/
def figure8WindowGeometry
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowGeometry
      D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.figure8WindowGeometry H

/-- Figure 9 adjacent-left window geometry from the boundary-extracted
explicit fields. -/
def figure9LeftWindowGeometry
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    HonestFigure9AdjacentLeftWindowGeometry
      D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.figure9LeftWindowGeometry H

/-- The boundary-extracted local labels use the stored boundary `p` labels. -/
@[simp]
theorem localLabels_p
    (_H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds)
    (i : M8BoundaryIndex) :
    D.toM8LocalLabels.labels.p i = D.spine.p i := by
  exact M8LabelsFromBoundaryData.toM8LocalLabels_p D i

@[simp]
theorem localLabels_q
    (_H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds)
    (i : M8TriangleIndex) :
    D.toM8LocalLabels.labels.q i = D.spine.q i :=
  M8LabelsFromBoundaryData.toM8LocalLabels_q D i

@[simp]
theorem localLabels_r
    (_H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.r i = D.lemma8.r i :=
  M8LabelsFromBoundaryData.toM8LocalLabels_r D i

@[simp]
theorem localLabels_s
    (_H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.s i = D.lemma8.s i :=
  M8LabelsFromBoundaryData.toM8LocalLabels_s D i

/-- Boundary-extracted fields give the honest E22 lower bound. -/
theorem figure8_E22
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.figure8_E22 H

/-- Boundary-extracted fields give the honest E23 lower bound. -/
theorem figure9_E23
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.figure9_E23 H

/-- Boundary-extracted fields give the paired honest E22/E23 lower bounds. -/
theorem E22_E23
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        D.toM8LocalLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.E22_E23 H

/-- Boundary-extracted fields give the paired E22/E23 bounds through the
construction-interface window-geometry projection. -/
theorem E22_E23_via_m8WindowGeometry
    (H : M8LabelsFromBoundaryWindowContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        D.toM8LocalLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.E22_E23_via_m8WindowGeometry H

end M8LabelsFromBoundaryWindowContainmentFields

/-- Concrete window-containment fields specialized to the finite boundary
label package. -/
abbrev M8BoundaryLabelPackageWindowContainmentFields
    {n : Nat} {C : _root_.UDConfig n}
    (D : M8BoundaryLabelPackage C) (turnBounds : M8TurnBounds) :
    Type :=
  M8LocalWindowContainmentFields D.toM8LocalLabels turnBounds

namespace M8BoundaryLabelPackageWindowContainmentFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {D : M8BoundaryLabelPackage C}
variable {turnBounds : M8TurnBounds}

/-- Boundary-label-package data with separately supplied exact Figure 8 and
Figure 9 containment interfaces. -/
def ofContainmentInterfaces
    (figure8 :
      Figure8SeparatedContainmentInterface
        (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
        turnBounds.turn)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterface
        (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
        turnBounds.turn) :
    M8BoundaryLabelPackageWindowContainmentFields D turnBounds :=
  M8LocalWindowContainmentFields.ofContainmentInterfaces
    (localLabels := D.toM8LocalLabels) (turnBounds := turnBounds)
    figure8 figure9_left

/-- Boundary-label-package data with a combined angle-containment bridge. -/
def ofAngleContainmentBridges
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
        turnBounds.turn) :
    M8BoundaryLabelPackageWindowContainmentFields D turnBounds :=
  M8LocalWindowContainmentFields.ofAngleContainmentBridges
    (localLabels := D.toM8LocalLabels) (turnBounds := turnBounds) A

/-- Boundary-label-package fields packaged as `M8WindowContainment`. -/
def toM8WindowContainment
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    M8WindowContainment D.toM8LocalLabels turnBounds :=
  M8LocalWindowContainmentFields.toM8WindowContainment H

/-- The exact Figure 8 containment field for the boundary-label package. -/
def figure8ContainmentInterface
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  M8LocalWindowContainmentFields.figure8ContainmentInterface H

/-- The exact Figure 9 adjacent-left containment field for the boundary-label
package. -/
def figure9LeftContainmentInterface
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  M8LocalWindowContainmentFields.figure9LeftContainmentInterface H

/-- Boundary-label-package fields repackaged as the combined
angle-containment bridge. -/
def toAngleContainmentBridges
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    AngleContainmentBridges
      (M8BrokenLatticeGood D.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  M8LocalWindowContainmentFields.toAngleContainmentBridges H

/-- Boundary-label-package fields packaged as construction-interface window
geometry. -/
def toM8WindowGeometry
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    M8WindowGeometry D.toM8LocalLabels turnBounds :=
  M8LocalWindowContainmentFields.toM8WindowGeometry H

/-- Figure 8 window geometry from the boundary-label-package explicit fields.
-/
def figure8WindowGeometry
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowGeometry
      D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.figure8WindowGeometry H

/-- Figure 9 adjacent-left window geometry from the boundary-label-package
explicit fields. -/
def figure9LeftWindowGeometry
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    HonestFigure9AdjacentLeftWindowGeometry
      D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.figure9LeftWindowGeometry H

@[simp]
theorem localLabels_p
    (_H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds)
    (i : M8BoundaryIndex) :
    D.toM8LocalLabels.labels.p i = D.spine.p i :=
  M8BoundaryLabelPackage.localLabels_p D i

@[simp]
theorem localLabels_q
    (_H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds)
    (i : M8TriangleIndex) :
    D.toM8LocalLabels.labels.q i = D.spine.q i :=
  M8BoundaryLabelPackage.localLabels_q D i

@[simp]
theorem localLabels_r
    (_H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.r i = D.lemma8.r i :=
  M8BoundaryLabelPackage.localLabels_r D i

@[simp]
theorem localLabels_s
    (_H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds)
    (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.s i = D.lemma8.s i :=
  M8BoundaryLabelPackage.localLabels_s D i

/-- Boundary-label-package fields give the honest E22 lower bound. -/
theorem figure8_E22
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.figure8_E22 H

/-- Boundary-label-package fields give the honest E23 lower bound. -/
theorem figure9_E23
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.figure9_E23 H

/-- Boundary-label-package fields give the paired honest E22/E23 lower
bounds. -/
theorem E22_E23
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        D.toM8LocalLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.E22_E23 H

/-- Boundary-label-package fields give the paired E22/E23 bounds through the
construction-interface window-geometry projection. -/
theorem E22_E23_via_m8WindowGeometry
    (H : M8BoundaryLabelPackageWindowContainmentFields D turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        D.toM8LocalLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        D.toM8LocalLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.E22_E23_via_m8WindowGeometry H

end M8BoundaryLabelPackageWindowContainmentFields

end M8WindowContainmentConcrete
end Swanepoel
end ErdosProblems1066

end
