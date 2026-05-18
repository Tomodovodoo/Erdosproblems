import ErdosProblems1066.Swanepoel.OuterAngleBudgetProofW15
import ErdosProblems1066.Swanepoel.LongArcFactsSelectionW16
import ErdosProblems1066.Swanepoel.BoundaryAnglesToBudgetW14
import ErdosProblems1066.Swanepoel.OuterBoundaryAngleW12
import ErdosProblems1066.Swanepoel.Lemma67ToBoundaryArcW14

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryBudgetLongArcConcreteW17

open BoundaryAnglesToBudgetW14
open BoundaryArcInstantiationW13
open BoundaryArcW12
open BoundaryWalkClassificationConcrete
open Lemma10Inequalities
open Lemma67ToBoundaryArcW14
open LongArcFactsSelectionW16
open NonconcaveArcBudgetFromBoundary
open OuterAngleBudgetProofW15
open OuterBoundaryInstantiationW13

universe u

noncomputable section

variable {n : Nat}
variable {C : _root_.UDConfig n}

abbrev ConfigGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  Lemma67ToBoundaryArcW14.CanonicalGraph C

def boundaryLongArcFactsOfLemma67Input
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (ConfigGraph C)}
    (Q : Lemma67BoundaryArcInput C D) :
    BoundaryLongArcFacts.{u} D :=
  Q.boundaryLongArcExistenceFields.toBoundaryLongArcFacts

@[simp]
theorem boundaryLongArcFactsOfLemma67Input_selectedRawTurn
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (ConfigGraph C)}
    (Q : Lemma67BoundaryArcInput C D) :
    (boundaryLongArcFactsOfLemma67Input Q).rawTurn
        (boundaryLongArcFactsOfLemma67Input Q).selectedLongArc =
      Q.boundaryLongArcExistenceFields.rawTurn
        Q.boundaryLongArcExistenceFields.selectedLongArc :=
  rfl

theorem boundaryLongArcFactsOfLemma67Input_boundaryBudgetData
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (ConfigGraph C)}
    (Q : Lemma67BoundaryArcInput C D) :
    (boundaryLongArcFactsOfLemma67Input Q).toNonconcaveArcBoundaryBudgetData =
      Q.arcBoundaryBudget :=
  rfl

variable {core : OuterBoundaryCore (ConfigGraph C)}

def actualWitnessOfConcreteAnglesAndLemma67
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    ActualOuterAngleBudgetWitness.{u} (ConfigGraph C) :=
  actualWitnessOfConcreteAnglesAndLongArcFacts
    classification angleWitness Subpolygon subpolygonData
    (boundaryLongArcFactsOfLemma67Input Q)

@[simp]
theorem actualWitnessOfConcreteAnglesAndLemma67_angleData
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    (actualWitnessOfConcreteAnglesAndLemma67
      classification angleWitness Subpolygon subpolygonData Q).angleData =
        actualAngleDataOfConcreteWitnesses classification angleWitness :=
  rfl

@[simp]
theorem actualWitnessOfConcreteAnglesAndLemma67_longArcFacts
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    (actualWitnessOfConcreteAnglesAndLemma67
      classification angleWitness Subpolygon subpolygonData Q).longArcFacts =
        boundaryLongArcFactsOfLemma67Input Q :=
  rfl

@[simp]
theorem actualWitnessOfConcreteAnglesAndLemma67_selectedRawTurn
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    (actualWitnessOfConcreteAnglesAndLemma67
      classification angleWitness Subpolygon subpolygonData Q).selectedRawTurn =
        Q.boundaryLongArcExistenceFields.rawTurn
          Q.boundaryLongArcExistenceFields.selectedLongArc :=
  rfl

def actualBudgetFieldsOfConcreteAnglesAndLemma67
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    ActualOuterBoundaryAngleBudgetFields
      (actualAngleDataOfConcreteWitnesses classification angleWitness)
      Subpolygon subpolygonData
      (Q.boundaryLongArcExistenceFields.rawTurn
        Q.boundaryLongArcExistenceFields.selectedLongArc) :=
  (actualWitnessOfConcreteAnglesAndLemma67
    classification angleWitness Subpolygon subpolygonData
    Q).toActualOuterBoundaryAngleBudgetFields

@[simp]
theorem actualBudgetFieldsOfConcreteAnglesAndLemma67_geometricAngleBudget
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    (actualBudgetFieldsOfConcreteAnglesAndLemma67
      classification angleWitness Subpolygon subpolygonData
      Q).geometricAngleBudget =
        totalTurn
          (Q.boundaryLongArcExistenceFields.rawTurn
            Q.boundaryLongArcExistenceFields.selectedLongArc) :=
  rfl

theorem actualBudgetFieldsOfConcreteAnglesAndLemma67_lt_pi_div_three
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    (actualBudgetFieldsOfConcreteAnglesAndLemma67
      classification angleWitness Subpolygon subpolygonData
      Q).geometricAngleBudget < Real.pi / 3 :=
  Q.boundaryLongArcExistenceFields.selectedLongArc_totalTurn_lt_pi_div_three

def boundaryArcInstantiationOfConcreteAnglesAndLemma67
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    BoundaryArcInstantiation
      (ActualPlanarBoundary
        (actualAngleDataOfConcreteWitnesses classification angleWitness)
        Subpolygon subpolygonData) :=
  LongArcFactsSelectionW16.ActualOuterAngleBudgetWitness.toBoundaryArcInstantiation
    (actualWitnessOfConcreteAnglesAndLemma67
      classification angleWitness Subpolygon subpolygonData Q)
    Q.boundaryArc

@[simp]
theorem boundaryArcInstantiationOfConcreteAnglesAndLemma67_rawTurn
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    (boundaryArcInstantiationOfConcreteAnglesAndLemma67
      classification angleWitness Subpolygon subpolygonData Q).rawTurn =
        Q.boundaryLongArcExistenceFields.rawTurn
          Q.boundaryLongArcExistenceFields.selectedLongArc :=
  rfl

@[simp]
theorem boundaryArcInstantiationOfConcreteAnglesAndLemma67_boundaryAngleBudget
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (ConfigGraph C))
    (Q :
      Lemma67BoundaryArcInput C
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    (boundaryArcInstantiationOfConcreteAnglesAndLemma67
      classification angleWitness Subpolygon subpolygonData
      Q).boundaryAngleBudget =
        (actualBudgetFieldsOfConcreteAnglesAndLemma67
          classification angleWitness Subpolygon subpolygonData
          Q).toBoundaryAngleBudget :=
  rfl

end

end BoundaryBudgetLongArcConcreteW17
end Swanepoel
end ErdosProblems1066
