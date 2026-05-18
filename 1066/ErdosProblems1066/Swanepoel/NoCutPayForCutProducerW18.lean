import ErdosProblems1066.Swanepoel.PayForCutConcreteInequalityW17
import ErdosProblems1066.Swanepoel.PointwiseRemainingRowAssemblyW17

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutPayForCutProducerW18

open CutVertexInterface
open MinimalGraphFacts
open NoCutFromMinimalityW16
open PayForCutArithmeticW16
open PayForCutConcreteInequalityW17
open PointwiseRemainingRowAssemblyW17

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}

abbrev PointwiseBasePayForCutInput
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) : Prop :=
  MinimalitySelectedPayForCut hmin

abbrev PointwiseBasePayForCutFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      PointwiseBasePayForCutInput C hmin

abbrev MinimalFailureNoCutFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : IsMinimalClearedFailure C),
      NoCutVertex C

abbrev MinimalFailureConcreteSideCardFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      ConcreteSelectedSideCardInequalityAll hmin

structure PointwiseNoCutPayForCutInput
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) : Prop where
  minimalitySelectedPayForCut : MinimalitySelectedPayForCut hmin
  noCutVertex : NoCutVertex C

namespace PointwiseNoCutPayForCutInput

variable {hmin : IsMinimalClearedFailure C}

theorem iff_minimalitySelectedPayForCut :
    PointwiseNoCutPayForCutInput C hmin <->
      MinimalitySelectedPayForCut hmin := by
  constructor
  case mp =>
    intro H
    exact H.minimalitySelectedPayForCut
  case mpr =>
    intro hpay
    exact
      { minimalitySelectedPayForCut := hpay
        noCutVertex :=
          noCutVertex_of_minimalitySelectedPayForCut hpay }

theorem iff_noCutVertex :
    PointwiseNoCutPayForCutInput C hmin <-> NoCutVertex C := by
  exact
    iff_minimalitySelectedPayForCut.trans
      (minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure hmin)

theorem iff_concreteSideCardInequalityAll :
    PointwiseNoCutPayForCutInput C hmin <->
      ConcreteSelectedSideCardInequalityAll hmin := by
  exact
    iff_minimalitySelectedPayForCut.trans
      (minimalitySelectedPayForCut_iff_concreteSideCardInequalityAll hmin)

end PointwiseNoCutPayForCutInput

def pointwiseNoCutPayForCutInput_of_minimalitySelectedPayForCut
    {hmin : IsMinimalClearedFailure C}
    (hpay : MinimalitySelectedPayForCut hmin) :
    PointwiseNoCutPayForCutInput C hmin :=
  (PointwiseNoCutPayForCutInput.iff_minimalitySelectedPayForCut).2 hpay

def pointwiseNoCutPayForCutInput_of_noCutVertex
    (hmin : IsMinimalClearedFailure C) (hno : NoCutVertex C) :
    PointwiseNoCutPayForCutInput C hmin :=
  (PointwiseNoCutPayForCutInput.iff_noCutVertex).2 hno

def pointwiseNoCutPayForCutInput_of_concreteSideCardInequalityAll
    (hmin : IsMinimalClearedFailure C)
    (hcard : ConcreteSelectedSideCardInequalityAll hmin) :
    PointwiseNoCutPayForCutInput C hmin :=
  (PointwiseNoCutPayForCutInput.iff_concreteSideCardInequalityAll).2 hcard

theorem minimalitySelectedPayForCut_of_noCutVertex
    (hmin : IsMinimalClearedFailure C) (hno : NoCutVertex C) :
    MinimalitySelectedPayForCut hmin :=
  (minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure hmin).2 hno

theorem noCutVertex_of_minimalitySelectedPayForCut
    {hmin : IsMinimalClearedFailure C}
    (hpay : MinimalitySelectedPayForCut hmin) :
    NoCutVertex C :=
  NoCutFromMinimalityW16.noCutVertex_of_minimalitySelectedPayForCut hpay

theorem pointwiseBasePayForCutInput_iff_noCutVertex
    (hmin : IsMinimalClearedFailure C) :
    PointwiseBasePayForCutInput C hmin <-> NoCutVertex C :=
  minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure hmin

theorem pointwiseBasePayForCutInput_iff_concreteSideCardInequalityAll
    (hmin : IsMinimalClearedFailure C) :
    PointwiseBasePayForCutInput C hmin <->
      ConcreteSelectedSideCardInequalityAll hmin :=
  minimalitySelectedPayForCut_iff_concreteSideCardInequalityAll hmin

theorem pointwiseBasePayForCutInput_iff_connectedNoCutFromMinimality
    (hmin : IsMinimalClearedFailure C) :
    PointwiseBasePayForCutInput C hmin <->
      ConnectedNoCutFromMinimality C hmin :=
  ConnectedNoCutFromMinimality.iff_minimalitySelectedPayForCut.symm

theorem pointwiseBasePayForCutFamily_iff_noCutFamily :
    PointwiseBasePayForCutFamily <-> MinimalFailureNoCutFamily := by
  constructor
  case mp =>
    intro H n C hmin
    exact
      (pointwiseBasePayForCutInput_iff_noCutVertex (C := C) hmin).1
        (H C hmin)
  case mpr =>
    intro H n C hmin
    exact
      (pointwiseBasePayForCutInput_iff_noCutVertex (C := C) hmin).2
        (H C hmin)

theorem pointwiseBasePayForCutFamily_iff_concreteSideCardFamily :
    PointwiseBasePayForCutFamily <->
      MinimalFailureConcreteSideCardFamily := by
  constructor
  case mp =>
    intro H n C hmin
    exact
      (pointwiseBasePayForCutInput_iff_concreteSideCardInequalityAll
        (C := C) hmin).1 (H C hmin)
  case mpr =>
    intro H n C hmin
    exact
      (pointwiseBasePayForCutInput_iff_concreteSideCardInequalityAll
        (C := C) hmin).2 (H C hmin)

theorem noCutFamily_iff_concreteSideCardFamily :
    MinimalFailureNoCutFamily <-> MinimalFailureConcreteSideCardFamily := by
  exact
    pointwiseBasePayForCutFamily_iff_noCutFamily.symm.trans
      pointwiseBasePayForCutFamily_iff_concreteSideCardFamily

def pointwiseNoCutPayForCutInput_of_baseInputs
    {hmin : IsMinimalClearedFailure C}
    (P : PointwiseW16BaseInputs.{u} C hmin) :
    PointwiseNoCutPayForCutInput C hmin where
  minimalitySelectedPayForCut := P.minimalitySelectedPayForCut
  noCutVertex := P.noCutVertex

theorem pointwiseBaseInputs_noCutVertex
    {hmin : IsMinimalClearedFailure C}
    (P : PointwiseW16BaseInputs.{u} C hmin) :
    NoCutVertex C :=
  (pointwiseNoCutPayForCutInput_of_baseInputs P).noCutVertex

theorem pointwiseBaseInputs_concreteSideCardInequalityAll
    {hmin : IsMinimalClearedFailure C}
    (P : PointwiseW16BaseInputs.{u} C hmin) :
    ConcreteSelectedSideCardInequalityAll hmin :=
  (PointwiseNoCutPayForCutInput.iff_concreteSideCardInequalityAll).1
    (pointwiseNoCutPayForCutInput_of_baseInputs P)

theorem cutVertexPartition_obstructs_pointwiseBasePayForCutInput
    (hmin : IsMinimalClearedFailure C)
    (Pcut : CutVertexPartition C) :
    Not (PointwiseBasePayForCutInput C hmin) := by
  intro hpay
  exact
    cutVertexPartition_obstructs_sideCardInequality hmin Pcut
      ((minimalitySelectedPayForCut_iff_sideCardInequality hmin).1 hpay)

theorem cutVertexPartition_obstructs_pointwiseNoCutPayForCutInput
    (hmin : IsMinimalClearedFailure C)
    (Pcut : CutVertexPartition C) :
    Not (PointwiseNoCutPayForCutInput C hmin) := by
  intro H
  exact
    cutVertexPartition_obstructs_pointwiseBasePayForCutInput
      hmin Pcut H.minimalitySelectedPayForCut

theorem cutVertexPartition_obstructs_concreteSideCardFamily_at
    (hmin : IsMinimalClearedFailure C)
    (Pcut : CutVertexPartition C) :
    Not (ConcreteSelectedSideCardInequalityAll hmin) :=
  cutVertexPartition_obstructs_concreteSideCardInequalityAll hmin Pcut

theorem cutVertexPartition_obstructs_pointwiseW16BaseInputs
    (hmin : IsMinimalClearedFailure C)
    (Pcut : CutVertexPartition C) :
    Not (Nonempty (PointwiseW16BaseInputs.{u} C hmin)) := by
  intro hbase
  cases hbase with
  | intro Pbase =>
      exact pointwiseBaseInputs_noCutVertex Pbase (Nonempty.intro Pcut)

theorem pointwiseW16BaseInputs_no_go_iff_cutPartition_obstructs_payForCut
    (hmin : IsMinimalClearedFailure C) :
    (forall _Pcut : CutVertexPartition C,
      Not (Nonempty (PointwiseW16BaseInputs.{u} C hmin))) <->
      (forall _Pcut : CutVertexPartition C,
        Not (PointwiseBasePayForCutInput C hmin)) := by
  constructor
  case mp =>
    intro _H Pcut
    exact cutVertexPartition_obstructs_pointwiseBasePayForCutInput hmin Pcut
  case mpr =>
    intro _H Pcut
    exact cutVertexPartition_obstructs_pointwiseW16BaseInputs hmin Pcut

end

end NoCutPayForCutProducerW18
end Swanepoel
end ErdosProblems1066
