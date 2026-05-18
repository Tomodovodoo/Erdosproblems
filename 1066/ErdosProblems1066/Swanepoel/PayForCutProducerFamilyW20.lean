import ErdosProblems1066.Swanepoel.PointwiseFamilyProducerW18
import ErdosProblems1066.Swanepoel.NoCutMinimalityClosureW19
import ErdosProblems1066.Swanepoel.NoCutPayForCutProducerW18
import ErdosProblems1066.Swanepoel.NoCutFromMinimalityW16
import ErdosProblems1066.Swanepoel.MinimalGraphFacts

set_option autoImplicit false

/-!
# W20 pay-for-cut producer family closure

This file isolates the W18 `PayForCutConcreteProducerFamily` target.  The
available no-cut/minimality stack does not give an unconditional no-cut family;
it identifies the exact remaining field.  The statements below construct the
producer family from each equivalent facade and expose the reverse conversions.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PayForCutProducerFamilyW20

open CutVertexInterface
open MinimalGraphFacts

noncomputable section

abbrev PayForCutConcreteProducerFamily : Type 1 :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev ConcreteSideCardFamily : Prop :=
  NoCutPayForCutProducerW18.MinimalFailureConcreteSideCardFamily

abbrev MinimalitySelectedPayForCutFamily : Prop :=
  NoCutFromMinimalityW16.MinimalitySelectedPayForCutFamily

abbrev PayForCutNoCutFieldFamily : Prop :=
  NoCutMinimalityClosureW19.PayForCutNoCutFieldFamily

abbrev MinimalFailureNoCutFamily : Prop :=
  NoCutPayForCutProducerW18.MinimalFailureNoCutFamily

abbrev NoCutMinimalityRemainingInputFamily : Type 1 :=
  NoCutFromMinimalityW16.NoCutMinimalityRemainingInputFamily

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

def concreteSideCardFamily_of_payForCutConcreteProducerFamily
    (F : PayForCutConcreteProducerFamily) :
    ConcreteSideCardFamily :=
  fun C hmin => F.row C hmin

def minimalitySelectedPayForCutFamily_of_payForCutConcreteProducerFamily
    (F : PayForCutConcreteProducerFamily) :
    MinimalitySelectedPayForCutFamily :=
  (NoCutPayForCutProducerW18.pointwiseBasePayForCutFamily_iff_concreteSideCardFamily).2
    (concreteSideCardFamily_of_payForCutConcreteProducerFamily F)

def payForCutNoCutFieldFamily_of_payForCutConcreteProducerFamily
    (F : PayForCutConcreteProducerFamily) :
    PayForCutNoCutFieldFamily :=
  minimalitySelectedPayForCutFamily_of_payForCutConcreteProducerFamily F

def noCutFamily_of_payForCutConcreteProducerFamily
    (F : PayForCutConcreteProducerFamily) :
    MinimalFailureNoCutFamily :=
  (NoCutPayForCutProducerW18.noCutFamily_iff_concreteSideCardFamily).2
    (concreteSideCardFamily_of_payForCutConcreteProducerFamily F)

theorem noCutVertex_of_payForCutConcreteProducerFamily
    (F : PayForCutConcreteProducerFamily)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    NoCutVertex C :=
  noCutFamily_of_payForCutConcreteProducerFamily F C hmin

theorem minimalitySelectedPayForCut_of_payForCutConcreteProducerFamily
    (F : PayForCutConcreteProducerFamily)
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    NoCutFromMinimalityW16.MinimalitySelectedPayForCut hmin :=
  payForCutNoCutFieldFamily_of_payForCutConcreteProducerFamily F C hmin

def payForCutConcreteProducerFamily_of_concreteSideCardFamily
    (H : ConcreteSideCardFamily) :
    PayForCutConcreteProducerFamily where
  row := fun C hmin => H C hmin

def payForCutConcreteProducerFamily_of_minimalitySelectedPayForCutFamily
    (H : MinimalitySelectedPayForCutFamily) :
    PayForCutConcreteProducerFamily :=
  payForCutConcreteProducerFamily_of_concreteSideCardFamily
    ((NoCutPayForCutProducerW18.pointwiseBasePayForCutFamily_iff_concreteSideCardFamily).1
      H)

def payForCutConcreteProducerFamily_of_payForCutNoCutFieldFamily
    (H : PayForCutNoCutFieldFamily) :
    PayForCutConcreteProducerFamily :=
  payForCutConcreteProducerFamily_of_minimalitySelectedPayForCutFamily H

def payForCutConcreteProducerFamily_of_noCutFamily
    (H : MinimalFailureNoCutFamily) :
    PayForCutConcreteProducerFamily :=
  payForCutConcreteProducerFamily_of_concreteSideCardFamily
    ((NoCutPayForCutProducerW18.noCutFamily_iff_concreteSideCardFamily).1 H)

def payForCutConcreteProducerFamily_of_noCutMinimalityRemainingInputFamily
    (H : NoCutMinimalityRemainingInputFamily) :
    PayForCutConcreteProducerFamily :=
  payForCutConcreteProducerFamily_of_payForCutNoCutFieldFamily
    (NoCutMinimalityClosureW19.payForCutNoCutFieldFamily_of_noCutMinimalityRemainingInputFamily
      H)

theorem nonempty_payForCutConcreteProducerFamily_iff_concreteSideCardFamily :
    Nonempty PayForCutConcreteProducerFamily <-> ConcreteSideCardFamily := by
  constructor
  case mp =>
    intro hF
    cases hF with
    | intro F =>
        exact concreteSideCardFamily_of_payForCutConcreteProducerFamily F
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (payForCutConcreteProducerFamily_of_concreteSideCardFamily H)

theorem nonempty_payForCutConcreteProducerFamily_iff_minimalitySelectedPayForCutFamily :
    Nonempty PayForCutConcreteProducerFamily <->
      MinimalitySelectedPayForCutFamily := by
  exact
    nonempty_payForCutConcreteProducerFamily_iff_concreteSideCardFamily.trans
      (NoCutPayForCutProducerW18.pointwiseBasePayForCutFamily_iff_concreteSideCardFamily).symm

theorem nonempty_payForCutConcreteProducerFamily_iff_payForCutNoCutFieldFamily :
    Nonempty PayForCutConcreteProducerFamily <->
      PayForCutNoCutFieldFamily :=
  nonempty_payForCutConcreteProducerFamily_iff_minimalitySelectedPayForCutFamily

theorem nonempty_payForCutConcreteProducerFamily_iff_noCutFamily :
    Nonempty PayForCutConcreteProducerFamily <-> MinimalFailureNoCutFamily := by
  exact
    nonempty_payForCutConcreteProducerFamily_iff_concreteSideCardFamily.trans
      (NoCutPayForCutProducerW18.noCutFamily_iff_concreteSideCardFamily).symm

theorem row_iff_payForCutNoCutField
    (hmin : IsMinimalClearedFailure C) :
    PayForCutConcreteInequalityW17.ConcreteSelectedSideCardInequalityAll
        hmin <->
      NoCutMinimalityClosureW19.PayForCutNoCutField C hmin := by
  exact
    (NoCutPayForCutProducerW18.pointwiseBasePayForCutInput_iff_concreteSideCardInequalityAll
      (C := C) hmin).symm

theorem row_iff_noCutVertex
    (hmin : IsMinimalClearedFailure C) :
    PayForCutConcreteInequalityW17.ConcreteSelectedSideCardInequalityAll
        hmin <->
      NoCutVertex C := by
  exact
    (row_iff_payForCutNoCutField (C := C) hmin).trans
      (NoCutMinimalityClosureW19.payForCutNoCutField_iff_noCutVertex
        (C := C) hmin)

theorem cutVertexPartition_obstructs_payForCutConcreteProducerFamily
    (F : PayForCutConcreteProducerFamily)
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    False :=
  NoCutPayForCutProducerW18.cutVertexPartition_obstructs_concreteSideCardFamily_at
    hmin P (F.row C hmin)

theorem cutVertexPartition_obstructs_nonempty_payForCutConcreteProducerFamily
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (Nonempty PayForCutConcreteProducerFamily) := by
  intro hF
  cases hF with
  | intro F =>
      exact cutVertexPartition_obstructs_payForCutConcreteProducerFamily F hmin P

end

end PayForCutProducerFamilyW20
end Swanepoel
end ErdosProblems1066
