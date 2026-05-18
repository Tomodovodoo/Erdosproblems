import ErdosProblems1066.Swanepoel.FigureWitnessConcreteAssemblyW17
import ErdosProblems1066.Swanepoel.WindowContainmentW10

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W18 Figure containment producer

This file is the W18 ownership surface for the Figure 8/Figure 9 inputs used
by `FigureWitnessConcreteAssemblyW17.PointwiseFigureWitnessConcreteFields`.

The only input kept in the producer records is the existing
`AngleContainmentBridges` interface.  The rest of the file repackages that
explicit angle-containment data into the W12 selected witnesses, the W16
pointwise adapters, and the W17 concrete witness fields.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureContainmentProducerW18

open AngleContainmentInterface
open Figure8WindowContainmentW16
open Figure9WindowContainmentW16
open FigureWitnessConcreteAssemblyW17
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma89WindowContainmentProofW15
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalGraphFacts
open WindowContainmentW10

universe u

variable {n : Nat} {C : _root_.UDConfig n}

/-! ## Local producer -/

/--
Explicit local Figure-containment production input.

This record does not hide separate Figure 8/Figure 9 endpoints: its single
field is the checked angle-containment interface from which those endpoints
are projected.
-/
structure LocalFigureContainmentProducer
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  angleContainment :
    AngleContainmentBridges
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn

namespace LocalFigureContainmentProducer

variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}
variable (P : LocalFigureContainmentProducer localLabels turnBounds)

/-- The Figure 8 separated-containment interface projected from angle data. -/
def figure8ContainmentInterface :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  P.angleContainment.figure8

/-- The Figure 9 adjacent-left containment interface projected from angle data. -/
def figure9LeftContainmentInterface :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood localLabels.predicates.data)
      turnBounds.turn :=
  P.angleContainment.figure9

/-- The producer as the W10 local angle-containment field. -/
def toLocalAngleContainmentFields :
    LocalAngleContainmentFields localLabels turnBounds where
  angleContainment := P.angleContainment

/-- The producer as concrete local window-containment fields. -/
def toLocalWindowContainmentFields :
    M8LocalWindowContainmentFields localLabels turnBounds :=
  M8LocalWindowContainmentFields.ofAngleContainmentBridges
    P.angleContainment

/-- The producer in the W17 local Figure witness field shape. -/
def toLocalFigureWitnessConcreteFields :
    LocalFigureWitnessConcreteFields localLabels turnBounds where
  figure8 := figure8ContainmentInterface P
  figure9_left := figure9LeftContainmentInterface P

/-- W12 selected Figure 8 data extracted from the producer. -/
def figure8DataWitnesses :
    Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
      localLabels.predicates turnBounds.turn :=
  Figure8ContainmentW12.dataWitnesses_of_containmentInterface
    (figure8ContainmentInterface P)

/-- W12 selected Figure 9 adjacent-window data extracted from the producer. -/
def figure9AdjacentWitnesses :
    Figure9ContainmentW12.HonestAdjacentWindowWitnesses
      localLabels.predicates turnBounds.turn :=
  Figure9ContainmentW12.witnesses_of_containmentInterface
    (figure9LeftContainmentInterface P)

/-- The W13 reduced selected-witness package obtained from the producer. -/
def figureWitnesses :
    FiguresAssemblyW13.HonestFigureContainmentWitnesses
      localLabels.predicates turnBounds.turn where
  figure8 := figure8DataWitnesses P
  figure9_left := figure9AdjacentWitnesses P

/-- The producer supplies the honest E22/E23 pair through W12 selected data. -/
theorem E22_E23
    (P : LocalFigureContainmentProducer localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  FiguresAssemblyW13.HonestFigureContainmentWitnesses.E22_E23
    (figureWitnesses P)

/-- The producer supplies the honest E22/E23 pair through the W17 fields. -/
theorem E22_E23_via_w17
    (P : LocalFigureContainmentProducer localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  LocalFigureWitnessConcreteFields.E22_E23
    (toLocalFigureWitnessConcreteFields P)

@[simp]
theorem toLocalWindowContainmentFields_figure8 :
    (toLocalWindowContainmentFields P).figure8 =
      figure8ContainmentInterface P :=
  rfl

@[simp]
theorem toLocalWindowContainmentFields_figure9_left :
    (toLocalWindowContainmentFields P).figure9_left =
      figure9LeftContainmentInterface P :=
  rfl

@[simp]
theorem toLocalFigureWitnessConcreteFields_figure8 :
    (toLocalFigureWitnessConcreteFields P).figure8 =
      figure8ContainmentInterface P :=
  rfl

@[simp]
theorem toLocalFigureWitnessConcreteFields_figure9_left :
    (toLocalFigureWitnessConcreteFields P).figure9_left =
      figure9LeftContainmentInterface P :=
  rfl

end LocalFigureContainmentProducer

/-! ## Direct constructors from existing angle-containment fields -/

/-- Build the local producer directly from the combined angle-containment bridge. -/
def localProducer_of_angleContainmentBridges
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    LocalFigureContainmentProducer localLabels turnBounds where
  angleContainment := A

/-- Build the local producer from the W10 local angle-containment field. -/
def localProducer_of_localAngleContainmentFields
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (A : LocalAngleContainmentFields localLabels turnBounds) :
    LocalFigureContainmentProducer localLabels turnBounds where
  angleContainment := A.angleContainment

/-- W17 local Figure fields produced directly from a combined angle bridge. -/
def localFigureWitnessConcreteFields_of_angleContainmentBridges
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    LocalFigureWitnessConcreteFields localLabels turnBounds :=
  LocalFigureContainmentProducer.toLocalFigureWitnessConcreteFields
    (localProducer_of_angleContainmentBridges
      (localLabels := localLabels) (turnBounds := turnBounds) A)

/-- W17 local Figure fields produced directly from W10 angle fields. -/
def localFigureWitnessConcreteFields_of_localAngleContainmentFields
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (A : LocalAngleContainmentFields localLabels turnBounds) :
    LocalFigureWitnessConcreteFields localLabels turnBounds :=
  LocalFigureContainmentProducer.toLocalFigureWitnessConcreteFields
    (localProducer_of_localAngleContainmentFields A)

/-! ## Pointwise producer for the W17 base row -/

variable {hmin : IsMinimalClearedFailure C}

/--
Pointwise Figure-containment production input for a fixed Lemma 8/Lemma 9
base row.

The field is the same explicit angle-containment bridge, specialized to the
boundary-derived local labels and turn bounds of the base row.
-/
structure PointwiseFigureContainmentProducer
    (B : PointwiseLemma89Base.{u} C hmin) where
  angleContainment :
    AngleContainmentBridges
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn

namespace PointwiseFigureContainmentProducer

variable {B : PointwiseLemma89Base.{u} C hmin}
variable (P : PointwiseFigureContainmentProducer B)

/-- Forget the pointwise producer to the local producer. -/
def toLocalProducer :
    LocalFigureContainmentProducer B.localLabels B.turnBounds where
  angleContainment := P.angleContainment

/-- The Figure 8 separated-containment interface for the pointwise row. -/
def figure8ContainmentInterface :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn :=
  P.angleContainment.figure8

/-- The Figure 9 adjacent-left containment interface for the pointwise row. -/
def figure9LeftContainmentInterface :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn :=
  P.angleContainment.figure9

/-- The pointwise producer as W10 local angle-containment fields. -/
def toLocalAngleContainmentFields :
    LocalAngleContainmentFields B.localLabels B.turnBounds :=
  LocalFigureContainmentProducer.toLocalAngleContainmentFields
    (toLocalProducer P)

/-- The pointwise producer as concrete local window-containment fields. -/
def toLocalWindowContainmentFields :
    M8LocalWindowContainmentFields B.localLabels B.turnBounds :=
  LocalFigureContainmentProducer.toLocalWindowContainmentFields
    (toLocalProducer P)

/-- The pointwise producer as the W17 local Figure witness fields. -/
def toLocalFigureWitnessConcreteFields :
    LocalFigureWitnessConcreteFields B.localLabels B.turnBounds :=
  LocalFigureContainmentProducer.toLocalFigureWitnessConcreteFields
    (toLocalProducer P)

/-- The pointwise producer in the exact W17 pointwise field shape. -/
def toPointwiseFigureWitnessConcreteFields :
    PointwiseFigureWitnessConcreteFields B where
  fields := toLocalFigureWitnessConcreteFields P

/-- The pointwise producer in the W15 missing-window field shape. -/
def toPointwiseMissingWindowContainmentFields :
    PointwiseMissingWindowContainmentFields B where
  figure8 := figure8ContainmentInterface P
  figure9_left := figure9LeftContainmentInterface P

/-- The pointwise producer in the W16 Figure 8-only adapter shape. -/
def toPointwiseFigure8WindowContainmentField :
    PointwiseFigure8WindowContainmentField B where
  figure8 := figure8ContainmentInterface P

/-- The pointwise producer in the W16 selected Figure 9 adapter shape. -/
def toPointwiseFigure9SelectedWindowContainmentFields :
    PointwiseFigure9SelectedWindowContainmentFields B where
  figure8 := figure8ContainmentInterface P
  figure9_left :=
    Figure9ContainmentW12.witnesses_of_containmentInterface
      (figure9LeftContainmentInterface P)

/-- The pointwise producer as the full W15 Lemma 8/Lemma 9 window row. -/
def toPointwiseLemma89WindowContainmentFields :
    PointwiseLemma89WindowContainmentFields.{u} C hmin where
  base := B
  windowFields := toPointwiseMissingWindowContainmentFields P

/-- W12 selected Figure 8 data extracted from the pointwise producer. -/
def figure8DataWitnesses :
    Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
      B.localLabels.predicates B.turnBounds.turn :=
  LocalFigureContainmentProducer.figure8DataWitnesses
    (toLocalProducer P)

/-- W12 selected Figure 9 data extracted from the pointwise producer. -/
def figure9AdjacentWitnesses :
    Figure9ContainmentW12.HonestAdjacentWindowWitnesses
      B.localLabels.predicates B.turnBounds.turn :=
  LocalFigureContainmentProducer.figure9AdjacentWitnesses
    (toLocalProducer P)

/-- The W13 reduced selected-witness package for the pointwise producer. -/
def figureWitnesses :
    FiguresAssemblyW13.HonestFigureContainmentWitnesses
      B.localLabels.predicates B.turnBounds.turn :=
  LocalFigureContainmentProducer.figureWitnesses
    (toLocalProducer P)

/-- The pointwise producer supplies the honest E22/E23 pair. -/
theorem E22_E23
    (P : PointwiseFigureContainmentProducer B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  LocalFigureContainmentProducer.E22_E23
    (toLocalProducer P)

/-- The pointwise producer supplies the Figure 8 E22 side through W16. -/
theorem figure8_E22
    (P : PointwiseFigureContainmentProducer B) :
    HonestFigure8SeparatedWindowLowerE22
      B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigure8WindowContainmentField.honestFigure8SeparatedWindowLowerE22
    (toPointwiseFigure8WindowContainmentField P)

/-- The pointwise producer supplies the Figure 9 E23 side through W16. -/
theorem figure9_E23
    (P : PointwiseFigureContainmentProducer B) :
    HonestFigure9AdjacentWindowLowerE23
      B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigure9SelectedWindowContainmentFields.figure9_E23
    (toPointwiseFigure9SelectedWindowContainmentFields P)

/-- The pointwise producer closes the localized Lemma 8/Lemma 9 contradiction. -/
theorem contradiction
    (P : PointwiseFigureContainmentProducer B) :
    False :=
  PointwiseFigure9SelectedWindowContainmentFields.contradiction
    (toPointwiseFigure9SelectedWindowContainmentFields P)

@[simp]
theorem toPointwiseFigureWitnessConcreteFields_fields :
    (toPointwiseFigureWitnessConcreteFields P).fields =
      toLocalFigureWitnessConcreteFields P :=
  rfl

@[simp]
theorem toPointwiseMissingWindowContainmentFields_figure8 :
    (toPointwiseMissingWindowContainmentFields P).figure8 =
      figure8ContainmentInterface P :=
  rfl

@[simp]
theorem toPointwiseMissingWindowContainmentFields_figure9_left :
    (toPointwiseMissingWindowContainmentFields P).figure9_left =
      figure9LeftContainmentInterface P :=
  rfl

@[simp]
theorem toPointwiseFigure9SelectedWindowContainmentFields_figure8 :
    (toPointwiseFigure9SelectedWindowContainmentFields P).figure8 =
      figure8ContainmentInterface P :=
  rfl

end PointwiseFigureContainmentProducer

/-! ## Pointwise direct constructors -/

/-- Build the pointwise producer directly from a combined angle bridge. -/
def pointwiseProducer_of_angleContainmentBridges
    {B : PointwiseLemma89Base.{u} C hmin}
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood B.localLabels.predicates.data)
        B.turnBounds.turn) :
    PointwiseFigureContainmentProducer B where
  angleContainment := A

/-- Build the pointwise producer from W10 local angle-containment fields. -/
def pointwiseProducer_of_localAngleContainmentFields
    {B : PointwiseLemma89Base.{u} C hmin}
    (A : LocalAngleContainmentFields B.localLabels B.turnBounds) :
    PointwiseFigureContainmentProducer B where
  angleContainment := A.angleContainment

/-- Build the pointwise producer from the W15 missing-window fields. -/
def pointwiseProducer_of_missingWindowContainmentFields
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseMissingWindowContainmentFields B) :
    PointwiseFigureContainmentProducer B where
  angleContainment :=
    M8LocalWindowContainmentFields.toAngleContainmentBridges
      (PointwiseMissingWindowContainmentFields.toLocalWindowContainmentFields W)

/-- W17 pointwise fields produced directly from a combined angle bridge. -/
def pointwiseFigureWitnessConcreteFields_of_angleContainmentBridges
    {B : PointwiseLemma89Base.{u} C hmin}
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood B.localLabels.predicates.data)
        B.turnBounds.turn) :
    PointwiseFigureWitnessConcreteFields B :=
  PointwiseFigureContainmentProducer.toPointwiseFigureWitnessConcreteFields
    (pointwiseProducer_of_angleContainmentBridges (B := B) A)

/-- W17 pointwise fields produced directly from W10 local angle fields. -/
def pointwiseFigureWitnessConcreteFields_of_localAngleContainmentFields
    {B : PointwiseLemma89Base.{u} C hmin}
    (A : LocalAngleContainmentFields B.localLabels B.turnBounds) :
    PointwiseFigureWitnessConcreteFields B :=
  PointwiseFigureContainmentProducer.toPointwiseFigureWitnessConcreteFields
    (pointwiseProducer_of_localAngleContainmentFields A)

/-- W17 pointwise fields produced directly from W15 missing-window fields. -/
def pointwiseFigureWitnessConcreteFields_of_missingWindowContainmentFields
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseMissingWindowContainmentFields B) :
    PointwiseFigureWitnessConcreteFields B :=
  PointwiseFigureContainmentProducer.toPointwiseFigureWitnessConcreteFields
    (pointwiseProducer_of_missingWindowContainmentFields W)

/-! ## Uniform pointwise family -/

/--
Uniform W18 Figure-containment producer family.

Every row supplies an explicit `AngleContainmentBridges` value for the base row
selected by the other W18 Swanepoel producers.
-/
structure FigureContainmentProducerFamily : Type (u + 1) where
  angleContainment :
    forall {n : Nat} {C : _root_.UDConfig n}
      {hmin : IsMinimalClearedFailure C}
      (B : PointwiseLemma89Base.{u} C hmin),
        AngleContainmentBridges
          (M8BrokenLatticeGood B.localLabels.predicates.data)
          B.turnBounds.turn

namespace FigureContainmentProducerFamily

variable (F : FigureContainmentProducerFamily.{u})

/-- Select the pointwise producer for one base row. -/
def pointwiseProducer
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u} C hmin) :
    PointwiseFigureContainmentProducer B where
  angleContainment := F.angleContainment B

/-- Select W17 pointwise Figure fields for one base row. -/
def pointwiseFigureWitnessConcreteFields
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u} C hmin) :
    PointwiseFigureWitnessConcreteFields B :=
  PointwiseFigureContainmentProducer.toPointwiseFigureWitnessConcreteFields
    (pointwiseProducer F B)

/-- Select W15 missing-window fields for one base row. -/
def pointwiseMissingWindowContainmentFields
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u} C hmin) :
    PointwiseMissingWindowContainmentFields B :=
  PointwiseFigureContainmentProducer.toPointwiseMissingWindowContainmentFields
    (pointwiseProducer F B)

/-- Select the W13 reduced Figure witnesses for one base row. -/
def figureWitnesses
    {n : Nat} {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (B : PointwiseLemma89Base.{u} C hmin) :
    FiguresAssemblyW13.HonestFigureContainmentWitnesses
      B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigureContainmentProducer.figureWitnesses
    (pointwiseProducer F B)

end FigureContainmentProducerFamily

end FigureContainmentProducerW18
end Swanepoel
end ErdosProblems1066

end
