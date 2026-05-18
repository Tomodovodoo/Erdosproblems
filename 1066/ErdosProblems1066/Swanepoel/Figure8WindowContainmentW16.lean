import ErdosProblems1066.Swanepoel.Lemma89WindowContainmentProofW15
import ErdosProblems1066.Swanepoel.Figure8ContainmentW12
import ErdosProblems1066.Swanepoel.FiguresAssemblyW13
import ErdosProblems1066.Swanepoel.FiguresToRefinedM8W13
import ErdosProblems1066.Swanepoel.E22E23BridgeW12
import ErdosProblems1066.Swanepoel.Lemma8WitnessW12

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W16 Figure 8 window-containment adapter

This file isolates the Figure 8 half of the W15 local window field.  The
input is the local Figure 8 containment interface already named by the W15
pointwise missing-field record, and the output is the honest E22 lower-bound
hypothesis for the same local labels and turn function.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Figure8WindowContainmentW16

open AngleContainmentInterface
open Figure8ContainmentW12
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma89WindowContainmentProofW15
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalGraphFacts

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}
variable {B : PointwiseLemma89Base.{u} C hmin}

/-- The Figure 8 portion of a fixed W15 pointwise row. -/
structure PointwiseFigure8WindowContainmentField
    (B : PointwiseLemma89Base.{u} C hmin) where
  figure8 :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn

namespace PointwiseFigure8WindowContainmentField

/-- W12 selected Figure 8 data from the pointwise Figure 8 field. -/
def dataWitnesses
    (F : PointwiseFigure8WindowContainmentField B) :
    Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
      B.localLabels.predicates B.turnBounds.turn :=
  Figure8ContainmentW12.dataWitnesses_of_containmentInterface F.figure8

/-- The pointwise Figure 8 field supplies the honest E22 lower bound. -/
theorem honestFigure8SeparatedWindowLowerE22
    (F : PointwiseFigure8WindowContainmentField B) :
    HonestFigure8SeparatedWindowLowerE22
      B.localLabels.predicates B.turnBounds.turn :=
  Figure8ContainmentW12.honestFigure8SeparatedWindowLowerE22_of_dataWitnesses
    (PointwiseFigure8WindowContainmentField.dataWitnesses F)

/-- Pointwise separated-window lower bound obtained from the Figure 8 field. -/
theorem separatedTurn_lower
    (F : PointwiseFigure8WindowContainmentField B)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood B.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood B.localLabels.predicates.data j)) :
    Real.pi / 3 <= separatedTurn B.turnBounds.turn i j :=
  PointwiseFigure8WindowContainmentField.honestFigure8SeparatedWindowLowerE22
    F hi hsep hj hbad_i hbad_j

end PointwiseFigure8WindowContainmentField

namespace PointwiseMissingWindowContainmentFields

/-- Forget a W15 missing-field row to its Figure 8 component. -/
def toFigure8WindowContainmentField
    (W : PointwiseMissingWindowContainmentFields B) :
    PointwiseFigure8WindowContainmentField B where
  figure8 := W.figure8

/-- The W15 Figure 8 component alone supplies the honest E22 lower bound. -/
theorem figure8_E22
    (W : PointwiseMissingWindowContainmentFields B) :
    HonestFigure8SeparatedWindowLowerE22
      B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigure8WindowContainmentField.honestFigure8SeparatedWindowLowerE22
    (PointwiseMissingWindowContainmentFields.toFigure8WindowContainmentField W)

/-- Pointwise separated-window lower bound from the W15 Figure 8 component. -/
theorem figure8_separatedTurn_lower
    (W : PointwiseMissingWindowContainmentFields B)
    {i j : Nat} (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (M8BrokenLatticeGood B.localLabels.predicates.data i))
    (hbad_j : Not (M8BrokenLatticeGood B.localLabels.predicates.data j)) :
    Real.pi / 3 <= separatedTurn B.turnBounds.turn i j :=
  PointwiseMissingWindowContainmentFields.figure8_E22
    W hi hsep hj hbad_i hbad_j

end PointwiseMissingWindowContainmentFields

namespace PointwiseLemma89WindowContainmentFields

variable (R : PointwiseLemma89WindowContainmentFields.{u} C hmin)

/-- The assembled W15 row exposes the Figure 8 honest E22 lower bound. -/
theorem figure8_E22 :
    HonestFigure8SeparatedWindowLowerE22
      R.localLabels.predicates R.turnBounds.turn :=
  PointwiseMissingWindowContainmentFields.figure8_E22
    (B := R.base) R.windowFields

end PointwiseLemma89WindowContainmentFields

end Figure8WindowContainmentW16
end Swanepoel
end ErdosProblems1066

end
