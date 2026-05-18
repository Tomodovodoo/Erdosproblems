import ErdosProblems1066.Swanepoel.FigureContainmentProducerW18

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W19 Figure witness closure

This file is the W19 closure surface from combined angle-containment bridge
inputs to the W17 pointwise Figure witness concrete fields.  It does not add
new geometry: every E22/E23 projection below is routed through the concrete
containment fields already exposed by W17 and W18.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureWitnessClosureW19

open AngleContainmentInterface
open FigureContainmentProducerW18
open FigureWitnessConcreteAssemblyW17
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma89WindowContainmentProofW15
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalGraphFacts
open WindowContainmentW10

universe u

variable {n : Nat} {C : _root_.UDConfig n}

/-! ## Local angle bridge input -/

/-- W19 local input in the same style as an angle-containment bridge producer. -/
structure LocalAngleContainmentBridgeProducerInput
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  angleContainment :
    AngleContainmentBridges
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn

namespace LocalAngleContainmentBridgeProducerInput

variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}
variable (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds)

/-- Forget the W19 input to the W18 local producer. -/
def toW18LocalProducer :
    LocalFigureContainmentProducer localLabels turnBounds where
  angleContainment := P.angleContainment

/-- The same input as the W10 local angle-containment field. -/
def toLocalAngleContainmentFields :
    LocalAngleContainmentFields localLabels turnBounds where
  angleContainment := P.angleContainment

/-- Concrete local containment fields obtained directly from the angle bridge. -/
def toLocalWindowContainmentFields :
    M8LocalWindowContainmentFields localLabels turnBounds :=
  M8LocalWindowContainmentFields.ofAngleContainmentBridges
    P.angleContainment

/-- W17 local Figure witness concrete fields obtained from the W18 adapter. -/
def toLocalFigureWitnessConcreteFields :
    LocalFigureWitnessConcreteFields localLabels turnBounds :=
  LocalFigureContainmentProducer.toLocalFigureWitnessConcreteFields
    (toW18LocalProducer P)

/-- The Figure 8 containment interface projected from the input. -/
def figure8ContainmentInterface :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  P.angleContainment.figure8

/-- The Figure 9 adjacent-left containment interface projected from the input. -/
def figure9LeftContainmentInterface :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  P.angleContainment.figure9

/-- E22/E23 reduced to the concrete local containment fields. -/
theorem localWindowContainment_E22_E23
    (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  M8LocalWindowContainmentFields.E22_E23
    (toLocalWindowContainmentFields P)

/-- E22/E23 reduced through the W17 local Figure witness concrete fields. -/
theorem figureWitnessFields_E22_E23
    (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  LocalFigureWitnessConcreteFields.E22_E23
    (toLocalFigureWitnessConcreteFields P)

/-- Main local W19 E22/E23 closure from a combined angle bridge. -/
theorem E22_E23
    (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  localWindowContainment_E22_E23 P

/-- Figure 8/E22 projection from the local W19 input. -/
theorem figure8_E22
    (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
      localLabels.predicates turnBounds.turn :=
  (E22_E23 P).1

/-- Figure 9/E23 projection from the local W19 input. -/
theorem figure9_E23
    (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
      localLabels.predicates turnBounds.turn :=
  (E22_E23 P).2

/-- Pointwise separated-window lower bound from the concrete containment field. -/
theorem figure8_E22_apply
    (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood localLabels.predicates.data j)) :
    Real.pi / 3 <= separatedTurn turnBounds.turn i j :=
  M8LocalWindowContainmentFields.figure8_E22_apply
    (toLocalWindowContainmentFields P) hi hsep hj hbad_i hbad_j

/-- Pointwise adjacent-window lower bound from the concrete containment field. -/
theorem figure9_E23_apply
    (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood localLabels.predicates.data (i + 1))) :
    Real.pi / 3 <= adjacentTurn turnBounds.turn i :=
  M8LocalWindowContainmentFields.figure9_E23_apply
    (toLocalWindowContainmentFields P) hi hi_next hbad_i hbad_next

@[simp]
theorem toLocalWindowContainmentFields_figure8 :
    (toLocalWindowContainmentFields P).figure8 =
      P.angleContainment.figure8 :=
  rfl

@[simp]
theorem toLocalWindowContainmentFields_figure9_left :
    (toLocalWindowContainmentFields P).figure9_left =
      P.angleContainment.figure9 :=
  rfl

@[simp]
theorem toLocalFigureWitnessConcreteFields_figure8 :
    (toLocalFigureWitnessConcreteFields P).figure8 =
      P.angleContainment.figure8 :=
  rfl

@[simp]
theorem toLocalFigureWitnessConcreteFields_figure9_left :
    (toLocalFigureWitnessConcreteFields P).figure9_left =
      P.angleContainment.figure9 :=
  rfl

end LocalAngleContainmentBridgeProducerInput

/-- Build local W17 Figure witness fields directly from a combined angle bridge. -/
def localFigureWitnessConcreteFields_of_angleContainmentBridges
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    LocalFigureWitnessConcreteFields localLabels turnBounds :=
  (LocalAngleContainmentBridgeProducerInput.mk A).toLocalFigureWitnessConcreteFields

/-! ## Pointwise angle bridge input -/

variable {hmin : IsMinimalClearedFailure C}

/--
W19 pointwise input in the style of an angle-containment bridge producer,
specialized to one fixed Lemma 8/Lemma 9 base row.
-/
structure PointwiseAngleContainmentBridgeProducerInput
    (B : PointwiseLemma89Base.{u} C hmin) where
  angleContainment :
    AngleContainmentBridges
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn

namespace PointwiseAngleContainmentBridgeProducerInput

variable {B : PointwiseLemma89Base.{u} C hmin}
variable (P : PointwiseAngleContainmentBridgeProducerInput B)

/-- Forget the W19 pointwise input to its local input. -/
def toLocalInput :
    LocalAngleContainmentBridgeProducerInput B.localLabels B.turnBounds where
  angleContainment := P.angleContainment

/-- Forget the W19 pointwise input to the W18 pointwise producer. -/
def toW18PointwiseProducer :
    PointwiseFigureContainmentProducer B where
  angleContainment := P.angleContainment

/-- Concrete local containment fields for this pointwise row. -/
def toLocalWindowContainmentFields :
    M8LocalWindowContainmentFields B.localLabels B.turnBounds :=
  LocalAngleContainmentBridgeProducerInput.toLocalWindowContainmentFields
    (toLocalInput P)

/-- W15 missing-window fields for this pointwise row. -/
def toPointwiseMissingWindowContainmentFields :
    PointwiseMissingWindowContainmentFields B where
  figure8 := P.angleContainment.figure8
  figure9_left := P.angleContainment.figure9

/-- W17 pointwise Figure witness concrete fields for this row. -/
def toPointwiseFigureWitnessConcreteFields :
    PointwiseFigureWitnessConcreteFields B :=
  PointwiseFigureContainmentProducer.toPointwiseFigureWitnessConcreteFields
    (toW18PointwiseProducer P)

/-- Full W15 pointwise window-containment row obtained from the input. -/
def toPointwiseLemma89WindowContainmentFields :
    PointwiseLemma89WindowContainmentFields.{u} C hmin where
  base := B
  windowFields := toPointwiseMissingWindowContainmentFields P

/-- E22/E23 reduced directly to concrete local containment fields. -/
theorem localWindowContainment_E22_E23
    (P : PointwiseAngleContainmentBridgeProducerInput B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  M8LocalWindowContainmentFields.E22_E23
    (toLocalWindowContainmentFields P)

/-- E22/E23 reduced through the W15 pointwise containment fields. -/
theorem missingWindowFields_E22_E23
    (P : PointwiseAngleContainmentBridgeProducerInput B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  PointwiseMissingWindowContainmentFields.E22_E23
    (toPointwiseMissingWindowContainmentFields P)

/-- E22/E23 reduced through the W17 pointwise Figure witness concrete fields. -/
theorem figureWitnessFields_E22_E23
    (P : PointwiseAngleContainmentBridgeProducerInput B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigureWitnessConcreteFields.E22_E23
    (toPointwiseFigureWitnessConcreteFields P)

/-- Main pointwise W19 E22/E23 closure from a combined angle bridge. -/
theorem E22_E23
    (P : PointwiseAngleContainmentBridgeProducerInput B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  localWindowContainment_E22_E23 P

/-- Figure 8/E22 projection from the pointwise W19 input. -/
theorem figure8_E22
    (P : PointwiseAngleContainmentBridgeProducerInput B) :
    HonestFigure8SeparatedWindowLowerE22
      B.localLabels.predicates B.turnBounds.turn :=
  (E22_E23 P).1

/-- Figure 9/E23 projection from the pointwise W19 input. -/
theorem figure9_E23
    (P : PointwiseAngleContainmentBridgeProducerInput B) :
    HonestFigure9AdjacentWindowLowerE23
      B.localLabels.predicates B.turnBounds.turn :=
  (E22_E23 P).2

/-- Pointwise separated-window lower bound for this row. -/
theorem figure8_E22_apply
    (P : PointwiseAngleContainmentBridgeProducerInput B)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood B.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood B.localLabels.predicates.data j)) :
    Real.pi / 3 <= separatedTurn B.turnBounds.turn i j :=
  M8LocalWindowContainmentFields.figure8_E22_apply
    (toLocalWindowContainmentFields P) hi hsep hj hbad_i hbad_j

/-- Pointwise adjacent-window lower bound for this row. -/
theorem figure9_E23_apply
    (P : PointwiseAngleContainmentBridgeProducerInput B)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (M8BrokenLatticeGood B.localLabels.predicates.data i))
    (hbad_next :
      Not (M8BrokenLatticeGood B.localLabels.predicates.data (i + 1))) :
    Real.pi / 3 <= adjacentTurn B.turnBounds.turn i :=
  M8LocalWindowContainmentFields.figure9_E23_apply
    (toLocalWindowContainmentFields P) hi hi_next hbad_i hbad_next

/-- The pointwise input closes the localized Lemma 8/Lemma 9 contradiction. -/
theorem contradiction
    (P : PointwiseAngleContainmentBridgeProducerInput B) :
    False :=
  PointwiseFigureContainmentProducer.contradiction
    (toW18PointwiseProducer P)

@[simp]
theorem toLocalWindowContainmentFields_figure8 :
    (toLocalWindowContainmentFields P).figure8 =
      P.angleContainment.figure8 :=
  rfl

@[simp]
theorem toLocalWindowContainmentFields_figure9_left :
    (toLocalWindowContainmentFields P).figure9_left =
      P.angleContainment.figure9 :=
  rfl

@[simp]
theorem toPointwiseMissingWindowContainmentFields_figure8 :
    (toPointwiseMissingWindowContainmentFields P).figure8 =
      P.angleContainment.figure8 :=
  rfl

@[simp]
theorem toPointwiseMissingWindowContainmentFields_figure9_left :
    (toPointwiseMissingWindowContainmentFields P).figure9_left =
      P.angleContainment.figure9 :=
  rfl

@[simp]
theorem toPointwiseFigureWitnessConcreteFields_fields :
    (toPointwiseFigureWitnessConcreteFields P).fields =
      LocalAngleContainmentBridgeProducerInput.toLocalFigureWitnessConcreteFields
        (toLocalInput P) :=
  rfl

end PointwiseAngleContainmentBridgeProducerInput

/-- Build W17 pointwise Figure witness fields directly from a combined bridge. -/
def pointwiseFigureWitnessConcreteFields_of_angleContainmentBridges
    {B : PointwiseLemma89Base.{u} C hmin}
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood B.localLabels.predicates.data)
        B.turnBounds.turn) :
    PointwiseFigureWitnessConcreteFields B :=
  PointwiseAngleContainmentBridgeProducerInput.toPointwiseFigureWitnessConcreteFields
    (PointwiseAngleContainmentBridgeProducerInput.mk A)

/-- Reduce a pointwise E22/E23 window obligation to one combined bridge. -/
theorem pointwise_E22_E23_of_angleContainmentBridges
    {B : PointwiseLemma89Base.{u} C hmin}
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood B.localLabels.predicates.data)
        B.turnBounds.turn) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  PointwiseAngleContainmentBridgeProducerInput.E22_E23
    (PointwiseAngleContainmentBridgeProducerInput.mk A)

/-! ## Uniform pointwise family -/

/--
Uniform W19 angle-containment bridge producer family.  Each pointwise base row
receives the combined Figure 8/Figure 9 bridge needed by W17.
-/
structure AngleContainmentBridgeProducerFamily : Type (u + 1) where
  angleContainment :
    forall {n : Nat} {C : _root_.UDConfig n}
      {hmin : IsMinimalClearedFailure C}
      (B : PointwiseLemma89Base.{u, u} C hmin),
        AngleContainmentBridges
          (M8BrokenLatticeGood B.localLabels.predicates.data)
          B.turnBounds.turn

namespace AngleContainmentBridgeProducerFamily

variable (F : AngleContainmentBridgeProducerFamily.{u})

/-- Forget the W19 family to the W18 Figure-containment producer family. -/
def toW18FigureContainmentProducerFamily :
    FigureContainmentProducerFamily.{u} where
  angleContainment := fun B => F.angleContainment B

/-- Select the W19 pointwise input for one base row. -/
def pointwiseInput
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u, u} C hmin) :
    PointwiseAngleContainmentBridgeProducerInput B where
  angleContainment := F.angleContainment B

/-- Select W17 pointwise Figure witness concrete fields for one base row. -/
def pointwiseFigureWitnessConcreteFields
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u, u} C hmin) :
    PointwiseFigureWitnessConcreteFields B :=
  PointwiseAngleContainmentBridgeProducerInput.toPointwiseFigureWitnessConcreteFields
    (pointwiseInput F B)

/-- Select concrete local containment fields for one base row. -/
def pointwiseLocalWindowContainmentFields
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u, u} C hmin) :
    M8LocalWindowContainmentFields B.localLabels B.turnBounds :=
  PointwiseAngleContainmentBridgeProducerInput.toLocalWindowContainmentFields
    (pointwiseInput F B)

/-- Select W15 missing-window fields for one base row. -/
def pointwiseMissingWindowContainmentFields
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u, u} C hmin) :
    PointwiseMissingWindowContainmentFields B :=
  PointwiseAngleContainmentBridgeProducerInput.toPointwiseMissingWindowContainmentFields
    (pointwiseInput F B)

/-- Family-level pointwise E22/E23 closure through concrete containment. -/
theorem pointwise_E22_E23
    (F : AngleContainmentBridgeProducerFamily.{u})
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u, u} C hmin) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  PointwiseAngleContainmentBridgeProducerInput.E22_E23
    (B := B)
    (AngleContainmentBridgeProducerFamily.pointwiseInput
      (F := F) (n := n) (C := C) (hmin := hmin) B)

/-- The family reduces each pointwise row to W17 concrete Figure fields. -/
theorem pointwiseFigureWitnessConcreteFields_E22_E23
    (F : AngleContainmentBridgeProducerFamily.{u})
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u, u} C hmin) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigureWitnessConcreteFields.E22_E23
    (B := B)
    (AngleContainmentBridgeProducerFamily.pointwiseFigureWitnessConcreteFields
      (F := F) (n := n) (C := C) (hmin := hmin) B)

end AngleContainmentBridgeProducerFamily

end FigureWitnessClosureW19
end Swanepoel
end ErdosProblems1066

end
