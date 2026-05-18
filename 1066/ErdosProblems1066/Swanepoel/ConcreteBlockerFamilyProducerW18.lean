import ErdosProblems1066.Swanepoel.PointwiseRemainingRowAssemblyW17
import ErdosProblems1066.Swanepoel.SwanepoelConcreteBlockerLedgerW17

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace ConcreteBlockerFamilyProducerW18

open MinimalGraphFacts
open PointwiseRemainingRowAssemblyW17
open SwanepoelConcreteBlockerLedgerW17

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/--
The exact external obligation for this SW7 adapter.  SW6 owns producing this
pointwise family; this file only repackages it into the W17 blocker ledger.
-/
abbrev PointwiseFamilyObligation : Type 1 :=
  PointwiseW16AssemblyFamily.{0}

def pointwiseConcreteBlockerFieldsOfW17
    (P : PointwiseW16AssemblyInputs.{u} C hmin) :
    PointwiseConcreteBlockerFields.{u, 0} C hmin where
  minimalitySelectedPayForCut := P.base.minimalitySelectedPayForCut
  planarBoundary := P.base.planarBoundary
  boundaryArcInstantiation := P.boundaryArcInstantiation
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  localWindowContainment := P.localWindowContainment

@[simp]
theorem pointwiseConcreteBlockerFieldsOfW17_toW15PointwiseInputs
    (P : PointwiseW16AssemblyInputs.{u} C hmin) :
    (pointwiseConcreteBlockerFieldsOfW17 P).toW15PointwiseInputs =
      P.toBoundaryArcLocalWindowInputs := by
  rfl

@[simp]
theorem pointwiseConcreteBlockerFieldsOfW17_toRemainingInputs
    (P : PointwiseW16AssemblyInputs.{u} C hmin) :
    RemainingInputConcreteAssemblyW15.BoundaryArcLocalWindowInputs.toPointwiseRemainingInputs
        ((pointwiseConcreteBlockerFieldsOfW17 P).toW15PointwiseInputs) =
      P.toPointwiseRemainingInputs := by
  rfl

def concreteBlockerInputFamilyOfPointwiseFamily
    (F : PointwiseFamilyObligation) :
    ConcreteBlockerInputFamily.{0} where
  row := fun C hmin =>
    pointwiseConcreteBlockerFieldsOfW17 (F.row C hmin)

@[simp]
theorem concreteBlockerInputFamilyOfPointwiseFamily_row
    (F : PointwiseFamilyObligation)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    (concreteBlockerInputFamilyOfPointwiseFamily F).row C hmin =
      pointwiseConcreteBlockerFieldsOfW17 (F.row C hmin) := by
  rfl

@[simp]
theorem concreteBlockerInputFamilyOfPointwiseFamily_w15_inputs
    (F : PointwiseFamilyObligation)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    (concreteBlockerInputFamilyOfPointwiseFamily F).toW15InputFamily.inputs
        C hmin =
      (F.row C hmin).toBoundaryArcLocalWindowInputs := by
  rfl

theorem no_minimalClearedFailure_of_pointwiseFamily
    (F : PointwiseFamilyObligation) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  (concreteBlockerInputFamilyOfPointwiseFamily F).no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne_of_pointwiseFamily
    (F : PointwiseFamilyObligation) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  (concreteBlockerInputFamilyOfPointwiseFamily F).targetLowerBoundEightThirtyOne

end

end ConcreteBlockerFamilyProducerW18
end Swanepoel
end ErdosProblems1066
