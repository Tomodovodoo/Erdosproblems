import ErdosProblems1066.Swanepoel.FigureContainmentProducerW18
import ErdosProblems1066.Swanepoel.Figure8ContainmentW12
import ErdosProblems1066.Swanepoel.Figure9ContainmentW12
import ErdosProblems1066.Swanepoel.Figure8WindowContainmentW16
import ErdosProblems1066.Swanepoel.Figure9WindowContainmentW16
import ErdosProblems1066.Swanepoel.M8WindowGeometryFromContainment
import ErdosProblems1066.Swanepoel.Lemma89WindowContainmentProofW15

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W19 angle-containment bridge producer

This file is the W19 ownership surface for the exact
`AngleContainmentBridges` input consumed by
`FigureContainmentProducerW18`.

The core certificate is intentionally minimal: W12 selected Figure 8/Figure 9
data, plus the uniform angle-containment hypotheses needed to rebuild the
older `AngleContainmentInterface` records.  The rest of the file provides
lossless conversions to the W16 selected rows, the W15 missing-window rows,
the M8 window-geometry package, and the W18 Figure-containment producers.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace AngleContainmentBridgeProducerW19

open AngleContainmentInterface
open AngleBridgeFacts
open AngleGeometry
open Figure8WindowContainmentW16
open Figure9WindowContainmentW16
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma89WindowContainmentProofW15
open M8ConstructionInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

abbrev Point : Type := AngleGeometry.Point

/-! ## Exact angle-containment certificates -/

/-- The uniform Figure 8 central-angle containment needed by
`Figure8SeparatedContainmentInterface`. -/
abbrev Figure8UniversalAngleContainment
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i j : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
    Figure8DistanceData p qi qj s r ->
      angleAt qi p qj <= separatedTurn turn i j

/-- The uniform Figure 9 left-angle containment needed by
`Figure9AdjacentLeftContainmentInterface`. -/
abbrev Figure9UniversalLeftAngleContainment
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  forall {i : Nat} {p qi qj s r : Point},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
    Figure9DistanceData p qi qj s r ->
      angleAt p qi s <= adjacentTurn turn i

/-- W12 Figure 8 selected data plus the exact universal containment proof
required to reconstruct the Figure 8 angle-containment interface. -/
structure Figure8ExactAngleContainmentCertificate
    (good : Nat -> Prop) (turn : Nat -> Real) where
  witnesses :
    Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn
  central_angle_le_separatedTurn :
    Figure8UniversalAngleContainment good turn

namespace Figure8ExactAngleContainmentCertificate

variable {good : Nat -> Prop} {turn : Nat -> Real}
variable (H : Figure8ExactAngleContainmentCertificate good turn)

/-- The selected raw Figure 8 extracted datum at a separated failed pair. -/
def extractedData
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    Figure8SeparatedExtractedData :=
  (H.witnesses hi hsep hj hbad_i hbad_j).toExtractedData

/-- Rebuild the exact Figure 8 containment interface from the certificate. -/
def toContainmentInterface :
    Figure8SeparatedContainmentInterface good turn where
  extractedData := by
    intro i j hi hsep hj hbad_i hbad_j
    exact H.extractedData hi hsep hj hbad_i hbad_j
  central_angle_le_separatedTurn := by
    intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
    exact H.central_angle_le_separatedTurn hi hsep hj hbad_i hbad_j D

/-- A preexisting Figure 8 containment interface gives the exact certificate. -/
def ofContainmentInterface
    (F : Figure8SeparatedContainmentInterface good turn) :
    Figure8ExactAngleContainmentCertificate good turn where
  witnesses := Figure8ContainmentW12.dataWitnesses_of_containmentInterface F
  central_angle_le_separatedTurn := F.central_angle_le_separatedTurn

/-- The certificate gives the Figure 8 E22 lower-bound field through W12. -/
theorem E22
    (H : Figure8ExactAngleContainmentCertificate good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  Figure8ContainmentW12.E22_of_dataWitnesses H.witnesses

/-- The certificate gives the Figure 8 E22 lower-bound field through the
rebuilt containment interface. -/
theorem E22_via_containmentInterface
    (H : Figure8ExactAngleContainmentCertificate good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  Figure8SeparatedContainmentInterface.separatedWindowLowerE22
    H.toContainmentInterface

@[simp]
theorem toContainmentInterface_extractedData
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j)) :
    H.toContainmentInterface.extractedData hi hsep hj hbad_i hbad_j =
      H.extractedData hi hsep hj hbad_i hbad_j :=
  rfl

end Figure8ExactAngleContainmentCertificate

/-- Forget a W12 Figure 9 datum to the raw extracted-data shape used by
`AngleContainmentInterface`. -/
def figure9ExtractedData_of_adjacentWindowData
    {turn : Nat -> Real} {i : Nat}
    (D : Figure9ContainmentW12.AdjacentWindowData turn i) :
    Figure9AdjacentExtractedData where
  p := D.p
  qi := D.qi
  qj := D.qj
  s := D.s
  r := D.r
  distanceData := D.distanceData

/-- W12 Figure 9 selected data plus the exact universal left-angle containment
proof required to reconstruct the Figure 9 angle-containment interface. -/
structure Figure9ExactAngleContainmentCertificate
    (good : Nat -> Prop) (turn : Nat -> Real) where
  witnesses :
    Figure9ContainmentW12.AdjacentWindowWitnesses good turn
  left_angle_le_adjacentTurn :
    Figure9UniversalLeftAngleContainment good turn

namespace Figure9ExactAngleContainmentCertificate

variable {good : Nat -> Prop} {turn : Nat -> Real}
variable (H : Figure9ExactAngleContainmentCertificate good turn)

/-- The selected raw Figure 9 extracted datum at an adjacent failed pair. -/
def extractedData
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    Figure9AdjacentExtractedData :=
  figure9ExtractedData_of_adjacentWindowData
    (H.witnesses hi hi_next hbad_i hbad_next)

/-- Rebuild the exact Figure 9 adjacent-left containment interface from the
certificate. -/
def toContainmentInterface :
    Figure9AdjacentLeftContainmentInterface good turn where
  extractedData := by
    intro i hi hi_next hbad_i hbad_next
    exact H.extractedData hi hi_next hbad_i hbad_next
  left_angle_le_adjacentTurn := by
    intro i p qi qj s r hi hi_next hbad_i hbad_next D
    exact H.left_angle_le_adjacentTurn hi hi_next hbad_i hbad_next D

/-- A preexisting Figure 9 containment interface gives the exact certificate. -/
def ofContainmentInterface
    (F : Figure9AdjacentLeftContainmentInterface good turn) :
    Figure9ExactAngleContainmentCertificate good turn where
  witnesses := Figure9ContainmentW12.witnesses_of_containmentInterface F
  left_angle_le_adjacentTurn := F.left_angle_le_adjacentTurn

/-- The certificate gives the Figure 9 E23 lower-bound field through W12. -/
theorem E23
    (H : Figure9ExactAngleContainmentCertificate good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  Figure9ContainmentW12.E23_of_witnesses H.witnesses

/-- The certificate gives the Figure 9 E23 lower-bound field through the
rebuilt containment interface. -/
theorem E23_via_containmentInterface
    (H : Figure9ExactAngleContainmentCertificate good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  Figure9AdjacentLeftContainmentInterface.adjacentWindowLowerE23
    H.toContainmentInterface

@[simp]
theorem toContainmentInterface_extractedData
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1))) :
    H.toContainmentInterface.extractedData hi hi_next hbad_i hbad_next =
      H.extractedData hi hi_next hbad_i hbad_next :=
  rfl

end Figure9ExactAngleContainmentCertificate

/-- Minimal exact certificate for both Figure 8 and Figure 9 angle
containment. -/
structure ExactAngleContainmentCertificate
    (good : Nat -> Prop) (turn : Nat -> Real) where
  figure8 : Figure8ExactAngleContainmentCertificate good turn
  figure9 : Figure9ExactAngleContainmentCertificate good turn

namespace ExactAngleContainmentCertificate

variable {good : Nat -> Prop} {turn : Nat -> Real}
variable (H : ExactAngleContainmentCertificate good turn)

/-- Rebuild the combined `AngleContainmentBridges` value required by W18. -/
def toAngleContainmentBridges :
    AngleContainmentBridges good turn where
  figure8 := H.figure8.toContainmentInterface
  figure9 := H.figure9.toContainmentInterface

/-- A preexisting combined bridge gives the exact W19 certificate. -/
def ofAngleContainmentBridges
    (A : AngleContainmentBridges good turn) :
    ExactAngleContainmentCertificate good turn where
  figure8 :=
    Figure8ExactAngleContainmentCertificate.ofContainmentInterface A.figure8
  figure9 :=
    Figure9ExactAngleContainmentCertificate.ofContainmentInterface A.figure9

/-- The certificate supplies the paired E22/E23 lower-bound fields. -/
theorem E22_E23
    (H : ExactAngleContainmentCertificate good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  AngleContainmentBridges.E22_E23 H.toAngleContainmentBridges

/-- The same E22/E23 pair routed through `M8WindowGeometryFromContainment`. -/
theorem E22_E23_via_windowGeometry
    (H : ExactAngleContainmentCertificate good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  M8WindowGeometryFromContainment.E22_E23_of_angleContainmentBridges_via_windowGeometry
    H.toAngleContainmentBridges

@[simp]
theorem toAngleContainmentBridges_figure8 :
    H.toAngleContainmentBridges.figure8 =
      H.figure8.toContainmentInterface :=
  rfl

@[simp]
theorem toAngleContainmentBridges_figure9 :
    H.toAngleContainmentBridges.figure9 =
      H.figure9.toContainmentInterface :=
  rfl

end ExactAngleContainmentCertificate

/-! ## Local and pointwise W18 constructors -/

variable {n : Nat} {C : _root_.UDConfig n}

/-- Exact W19 certificate specialized to fixed M8 local labels. -/
abbrev LocalExactAngleContainmentCertificate
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  ExactAngleContainmentCertificate
    (M8BrokenLatticeGood localLabels.predicates.data)
    turnBounds.turn

namespace LocalExactAngleContainmentCertificate

variable {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
variable (H : LocalExactAngleContainmentCertificate localLabels turnBounds)

/-- The local certificate as concrete M8 local window-containment fields. -/
def toLocalWindowContainmentFields :
    M8LocalWindowContainmentFields localLabels turnBounds :=
  M8LocalWindowContainmentFields.ofAngleContainmentBridges
    H.toAngleContainmentBridges

/-- The local certificate as construction-interface M8 window geometry. -/
def toM8WindowGeometry :
    M8ConstructionInterface.M8WindowGeometry localLabels turnBounds :=
  H.toLocalWindowContainmentFields.toM8WindowGeometry

/-- The local certificate as the W18 local producer. -/
def toLocalFigureContainmentProducer :
    FigureContainmentProducerW18.LocalFigureContainmentProducer
      localLabels turnBounds :=
  FigureContainmentProducerW18.localProducer_of_angleContainmentBridges
    H.toAngleContainmentBridges

/-- The local certificate as W17 local Figure witness fields. -/
def toLocalFigureWitnessConcreteFields :
    FigureWitnessConcreteAssemblyW17.LocalFigureWitnessConcreteFields
      localLabels turnBounds :=
  H.toLocalFigureContainmentProducer.toLocalFigureWitnessConcreteFields

/-- Local paired E22/E23 lower-bound fields from the W18 producer route. -/
theorem E22_E23
    (H : LocalExactAngleContainmentCertificate localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  FigureContainmentProducerW18.LocalFigureContainmentProducer.E22_E23
    H.toLocalFigureContainmentProducer

/-- Local paired E22/E23 lower-bound fields through M8 window geometry. -/
theorem E22_E23_via_m8WindowGeometry
    (H : LocalExactAngleContainmentCertificate localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.E22_E23_via_m8WindowGeometry
    H.toLocalWindowContainmentFields

end LocalExactAngleContainmentCertificate

variable {hmin : IsMinimalClearedFailure C}

/-- Exact W19 certificate specialized to a fixed Lemma 8/Lemma 9 base row. -/
abbrev PointwiseExactAngleContainmentCertificate
    (B : PointwiseLemma89Base.{u} C hmin) :=
  ExactAngleContainmentCertificate
    (M8BrokenLatticeGood B.localLabels.predicates.data)
    B.turnBounds.turn

namespace PointwiseExactAngleContainmentCertificate

variable {B : PointwiseLemma89Base.{u} C hmin}
variable (H : PointwiseExactAngleContainmentCertificate B)

/-- The pointwise certificate as a W16 Figure 8-only field. -/
def toPointwiseFigure8WindowContainmentField :
    PointwiseFigure8WindowContainmentField B where
  figure8 := H.toAngleContainmentBridges.figure8

/-- The pointwise certificate as the W16 selected Figure 9 row. -/
def toPointwiseFigure9SelectedWindowContainmentFields :
    PointwiseFigure9SelectedWindowContainmentFields B where
  figure8 := H.toAngleContainmentBridges.figure8
  figure9_left := H.figure9.witnesses

/-- The pointwise certificate as the W15 missing-window row. -/
def toPointwiseMissingWindowContainmentFields :
    PointwiseMissingWindowContainmentFields B where
  figure8 := H.toAngleContainmentBridges.figure8
  figure9_left := H.toAngleContainmentBridges.figure9

/-- The pointwise certificate as concrete local window-containment fields. -/
def toLocalWindowContainmentFields :
    M8LocalWindowContainmentFields B.localLabels B.turnBounds :=
  H.toPointwiseMissingWindowContainmentFields.toLocalWindowContainmentFields

/-- The pointwise certificate as the W18 pointwise producer. -/
def toPointwiseFigureContainmentProducer :
    FigureContainmentProducerW18.PointwiseFigureContainmentProducer B :=
  FigureContainmentProducerW18.pointwiseProducer_of_angleContainmentBridges
    H.toAngleContainmentBridges

/-- The pointwise certificate as W17 pointwise Figure witness fields. -/
def toPointwiseFigureWitnessConcreteFields :
    FigureWitnessConcreteAssemblyW17.PointwiseFigureWitnessConcreteFields B :=
  H.toPointwiseFigureContainmentProducer
    |>.toPointwiseFigureWitnessConcreteFields

/-- The pointwise certificate supplies the paired E22/E23 fields. -/
theorem E22_E23
    (H : PointwiseExactAngleContainmentCertificate B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  FigureContainmentProducerW18.PointwiseFigureContainmentProducer.E22_E23
    H.toPointwiseFigureContainmentProducer

/-- The pointwise certificate closes the localized Lemma 8/Lemma 9 row. -/
theorem contradiction
    (H : PointwiseExactAngleContainmentCertificate B) :
    False :=
  FigureContainmentProducerW18.PointwiseFigureContainmentProducer.contradiction
    H.toPointwiseFigureContainmentProducer

end PointwiseExactAngleContainmentCertificate

/-! ## Constructors from existing W15 and W16 fields -/

/-- W15 missing-window fields are exactly a combined angle-containment bridge. -/
def angleContainmentBridges_of_missingWindowContainmentFields
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseMissingWindowContainmentFields B) :
    AngleContainmentBridges
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn where
  figure8 := W.figure8
  figure9 := W.figure9_left

/-- W15 missing-window fields as the exact W19 pointwise certificate. -/
def exactCertificate_of_missingWindowContainmentFields
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseMissingWindowContainmentFields B) :
    PointwiseExactAngleContainmentCertificate B :=
  ExactAngleContainmentCertificate.ofAngleContainmentBridges
    (angleContainmentBridges_of_missingWindowContainmentFields W)

/-- W15 missing-window fields as the W18 pointwise Figure-containment
producer. -/
def pointwiseProducer_of_missingWindowContainmentFields
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseMissingWindowContainmentFields B) :
    FigureContainmentProducerW18.PointwiseFigureContainmentProducer B :=
  FigureContainmentProducerW18.pointwiseProducer_of_angleContainmentBridges
    (angleContainmentBridges_of_missingWindowContainmentFields W)

/-- W15 assembled rows as the W18 pointwise Figure-containment producer. -/
def pointwiseProducer_of_lemma89WindowContainmentFields
    (R : PointwiseLemma89WindowContainmentFields.{u} C hmin) :
    FigureContainmentProducerW18.PointwiseFigureContainmentProducer R.base :=
  pointwiseProducer_of_missingWindowContainmentFields R.windowFields

/-- W16 selected Figure 9 fields plus the exact universal Figure 9
containment needed to rebuild the W15/W18 interface. -/
structure PointwiseFigure9SelectedExactAngleContainmentCertificate
    (B : PointwiseLemma89Base.{u} C hmin) where
  selected : PointwiseFigure9SelectedWindowContainmentFields B
  figure9_left_angle_le_adjacentTurn :
    Figure9UniversalLeftAngleContainment
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn

namespace PointwiseFigure9SelectedExactAngleContainmentCertificate

variable {B : PointwiseLemma89Base.{u} C hmin}
variable (H : PointwiseFigure9SelectedExactAngleContainmentCertificate B)

/-- Rebuild the Figure 9 adjacent-left containment interface from the W16
selected witnesses and the exact universal left-angle containment proof. -/
def figure9LeftContainmentInterface :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn where
  extractedData := by
    intro i hi hi_next hbad_i hbad_next
    exact
      figure9ExtractedData_of_adjacentWindowData
        (H.selected.figure9_left hi hi_next hbad_i hbad_next)
  left_angle_le_adjacentTurn := by
    intro i p qi qj s r hi hi_next hbad_i hbad_next D
    exact H.figure9_left_angle_le_adjacentTurn
      hi hi_next hbad_i hbad_next D

/-- Rebuild the W15 missing-window row from the W16 selected row and exact
angle containment. -/
def toPointwiseMissingWindowContainmentFields :
    PointwiseMissingWindowContainmentFields B where
  figure8 := H.selected.figure8
  figure9_left := H.figure9LeftContainmentInterface

/-- Rebuild the combined W18 angle-containment bridge. -/
def toAngleContainmentBridges :
    AngleContainmentBridges
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn :=
  angleContainmentBridges_of_missingWindowContainmentFields
    H.toPointwiseMissingWindowContainmentFields

/-- The W16 selected/exact certificate as a pointwise exact W19 certificate. -/
def toPointwiseExactAngleContainmentCertificate :
    PointwiseExactAngleContainmentCertificate B :=
  ExactAngleContainmentCertificate.ofAngleContainmentBridges
    H.toAngleContainmentBridges

/-- The W16 selected/exact certificate as the W18 pointwise producer. -/
def toPointwiseFigureContainmentProducer :
    FigureContainmentProducerW18.PointwiseFigureContainmentProducer B :=
  FigureContainmentProducerW18.pointwiseProducer_of_angleContainmentBridges
    H.toAngleContainmentBridges

/-- The rebuilt producer supplies the paired E22/E23 lower-bound fields. -/
theorem E22_E23
    (H : PointwiseFigure9SelectedExactAngleContainmentCertificate B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  FigureContainmentProducerW18.PointwiseFigureContainmentProducer.E22_E23
    H.toPointwiseFigureContainmentProducer

/-- The original W16 selected row already closes the localized contradiction. -/
theorem contradiction_via_w16
    (H : PointwiseFigure9SelectedExactAngleContainmentCertificate B) :
    False :=
  PointwiseFigure9SelectedWindowContainmentFields.contradiction H.selected

end PointwiseFigure9SelectedExactAngleContainmentCertificate

/-! ## Uniform family constructor for W18 -/

/-- Uniform exact angle-containment certificates for the W18 Figure producer. -/
structure ExactAngleContainmentCertificateFamily : Type (u + 1) where
  certificate :
    forall {n : Nat} {C : _root_.UDConfig n}
      {hmin : IsMinimalClearedFailure C}
      (B : PointwiseLemma89Base.{u} C hmin),
        PointwiseExactAngleContainmentCertificate B

namespace ExactAngleContainmentCertificateFamily

variable (F : ExactAngleContainmentCertificateFamily.{u})

/-- Select the combined angle bridge for one pointwise base row. -/
def angleContainment
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u} C hmin) :
    AngleContainmentBridges
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn :=
  (F.certificate B).toAngleContainmentBridges

/-- Select the W18 pointwise producer for one pointwise base row. -/
def pointwiseProducer
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u} C hmin) :
    FigureContainmentProducerW18.PointwiseFigureContainmentProducer B :=
  (F.certificate B).toPointwiseFigureContainmentProducer

/-- Convert the exact W19 family to the W18 Figure-containment producer
family. -/
def toFigureContainmentProducerFamily :
    FigureContainmentProducerW18.FigureContainmentProducerFamily.{u} where
  angleContainment := by
    intro n C hmin B
    exact F.angleContainment B

/-- The W19 family supplies W17 pointwise Figure witness fields through W18. -/
def pointwiseFigureWitnessConcreteFields
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u} C hmin) :
    FigureWitnessConcreteAssemblyW17.PointwiseFigureWitnessConcreteFields B :=
  F.toFigureContainmentProducerFamily.pointwiseFigureWitnessConcreteFields B

@[simp]
theorem toFigureContainmentProducerFamily_angleContainment
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u} C hmin) :
    F.toFigureContainmentProducerFamily.angleContainment B =
      F.angleContainment B :=
  rfl

end ExactAngleContainmentCertificateFamily

end AngleContainmentBridgeProducerW19
end Swanepoel
end ErdosProblems1066

end
