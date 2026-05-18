import ErdosProblems1066.Swanepoel.NoCutFromMinimalityW16
import ErdosProblems1066.Swanepoel.NoCutMinimalityProofW15
import ErdosProblems1066.Swanepoel.NoCutPayForCutProducerW18
import ErdosProblems1066.Swanepoel.MinimalGraphFacts

set_option autoImplicit false

/-!
# W19 no-cut minimality closure

This file records the exact status of the pay-for-cut/no-cut step for a
minimal cleared failure.  Minimality gives connectedness outright, while the
remaining no-cut contribution is precisely the W15 minimality-selected
pay-for-cut field.

The theorem surface below does not assert an unconditional no-cut theorem.
Instead it names the sharp remaining field and proves that, under
`IsMinimalClearedFailure`, this field is equivalent to the no-cut branch and
to the W18 pointwise/family pay-for-cut facades.  A supplied cut partition
refutes the field pointwise, which exposes the remaining obligation exactly.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutMinimalityClosureW19

open CutVertexInterface
open MinimalGraphFacts

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}

/-- The exact remaining minimality field needed to close the no-cut branch:
the side witnesses selected from minimality pay for every supplied cut
partition. -/
abbrev PayForCutNoCutField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) : Prop :=
  NoCutFromMinimalityW16.MinimalitySelectedPayForCut hmin

/-- Partition-level version of the exact remaining field. -/
abbrev PartitionPayForCutNoCutField
    (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C) : Prop :=
  NoCutMinimalityProofW15.MinimalitySelectedPartitionPaysCut hmin P

/-- Uniform version of the remaining field over all minimal cleared failures. -/
abbrev PayForCutNoCutFieldFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      PayForCutNoCutField C hmin

theorem payForCutNoCutField_iff_minimalitySelectedPayForCut
    (hmin : IsMinimalClearedFailure C) :
    PayForCutNoCutField C hmin <->
      NoCutFromMinimalityW16.MinimalitySelectedPayForCut hmin := by
  rfl

/-- Pointwise closure statement: the remaining field is exactly no-cut. -/
theorem payForCutNoCutField_iff_noCutVertex
    (hmin : IsMinimalClearedFailure C) :
    PayForCutNoCutField C hmin <-> NoCutVertex C :=
  NoCutPayForCutProducerW18.pointwiseBasePayForCutInput_iff_noCutVertex
    (C := C) hmin

theorem noCutVertex_of_payForCutNoCutField
    {hmin : IsMinimalClearedFailure C}
    (hfield : PayForCutNoCutField C hmin) :
    NoCutVertex C :=
  (payForCutNoCutField_iff_noCutVertex (C := C) hmin).1 hfield

theorem payForCutNoCutField_of_noCutVertex
    (hmin : IsMinimalClearedFailure C) (hno : NoCutVertex C) :
    PayForCutNoCutField C hmin :=
  (payForCutNoCutField_iff_noCutVertex (C := C) hmin).2 hno

/-- Minimality already supplies the connectedness component; the named field
adds exactly the no-cut component. -/
theorem payForCutNoCutField_iff_connectedNoCutFromMinimality
    (hmin : IsMinimalClearedFailure C) :
    PayForCutNoCutField C hmin <->
      NoCutFromMinimalityW16.ConnectedNoCutFromMinimality C hmin :=
  NoCutPayForCutProducerW18.pointwiseBasePayForCutInput_iff_connectedNoCutFromMinimality
    (C := C) hmin

def connectedNoCutFromMinimality_of_payForCutNoCutField
    {hmin : IsMinimalClearedFailure C}
    (hfield : PayForCutNoCutField C hmin) :
    NoCutFromMinimalityW16.ConnectedNoCutFromMinimality C hmin :=
  (payForCutNoCutField_iff_connectedNoCutFromMinimality (C := C) hmin).1
    hfield

theorem connected_of_payForCutNoCutField
    {hmin : IsMinimalClearedFailure C}
    (_hfield : PayForCutNoCutField C hmin) :
    (GraphBridge.unitDistanceSimpleGraph C).Connected :=
  NoCutMinimalityProofW15.connected_of_minimalFailure hmin

/-- W18's pointwise facade has the same content as the named remaining field. -/
theorem payForCutNoCutField_iff_pointwiseNoCutPayForCutInput
    (hmin : IsMinimalClearedFailure C) :
    PayForCutNoCutField C hmin <->
      NoCutPayForCutProducerW18.PointwiseNoCutPayForCutInput C hmin := by
  constructor
  case mp =>
    intro hfield
    exact
      NoCutPayForCutProducerW18.pointwiseNoCutPayForCutInput_of_minimalitySelectedPayForCut
        (C := C) hfield
  case mpr =>
    intro H
    exact H.minimalitySelectedPayForCut

def pointwiseNoCutPayForCutInput_of_payForCutNoCutField
    {hmin : IsMinimalClearedFailure C}
    (hfield : PayForCutNoCutField C hmin) :
    NoCutPayForCutProducerW18.PointwiseNoCutPayForCutInput C hmin :=
  (payForCutNoCutField_iff_pointwiseNoCutPayForCutInput (C := C) hmin).1
    hfield

/-- A supplied cut partition is exactly an obstruction to the remaining field. -/
theorem cutVertexPartition_obstructs_payForCutNoCutField
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (PayForCutNoCutField C hmin) :=
  NoCutMinimalityProofW15.cutVertexPartition_obstructs_minimalitySelectedPayForCut
    hmin P

/-- A supplied cut partition refutes its own partition-level field. -/
theorem cutVertexPartition_obstructs_partitionPayForCutNoCutField
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (PartitionPayForCutNoCutField hmin P) :=
  NoCutMinimalityProofW15.not_minimalitySelectedPartitionPaysCut_of_minimalFailure_partition
    hmin P

/-- Pointwise split: either the no-cut branch is already closed, or an actual
cut partition displays the failed partition-level pay-for-cut field. -/
theorem noCutVertex_or_exists_failed_partitionPayForCutNoCutField
    (hmin : IsMinimalClearedFailure C) :
    Or (NoCutVertex C)
      (Exists fun P : CutVertexPartition C =>
        Not (PartitionPayForCutNoCutField hmin P)) := by
  by_cases hno : NoCutVertex C
  case pos =>
    exact Or.inl hno
  case neg =>
    have hpart : Nonempty (CutVertexPartition C) := by
      exact Classical.not_not.mp (by
        simpa [NoCutVertex] using hno)
    cases hpart with
    | intro P =>
        exact Or.inr
          (Exists.intro P
            (cutVertexPartition_obstructs_partitionPayForCutNoCutField
              hmin P))

/-- Family closure statement: the uniform remaining field is exactly the
uniform no-cut family. -/
theorem payForCutNoCutFieldFamily_iff_noCutFamily :
    PayForCutNoCutFieldFamily <->
      NoCutPayForCutProducerW18.MinimalFailureNoCutFamily :=
  NoCutPayForCutProducerW18.pointwiseBasePayForCutFamily_iff_noCutFamily

theorem noCutFamily_of_payForCutNoCutFieldFamily
    (H : PayForCutNoCutFieldFamily) :
    NoCutPayForCutProducerW18.MinimalFailureNoCutFamily :=
  payForCutNoCutFieldFamily_iff_noCutFamily.1 H

theorem payForCutNoCutFieldFamily_of_noCutFamily
    (H : NoCutPayForCutProducerW18.MinimalFailureNoCutFamily) :
    PayForCutNoCutFieldFamily :=
  payForCutNoCutFieldFamily_iff_noCutFamily.2 H

/-- The W16 family facade's pay-for-cut component is exactly the named family
field. -/
theorem payForCutNoCutFieldFamily_of_noCutMinimalityRemainingInputFamily
    (H : NoCutFromMinimalityW16.NoCutMinimalityRemainingInputFamily) :
    PayForCutNoCutFieldFamily :=
  H.minimalitySelectedPayForCutFamily

end

end NoCutMinimalityClosureW19
end Swanepoel
end ErdosProblems1066
