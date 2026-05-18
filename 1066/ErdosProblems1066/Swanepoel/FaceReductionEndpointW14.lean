import ErdosProblems1066.Swanepoel.SubpolygonFaceReductionW14
import ErdosProblems1066.Swanepoel.RemainingInputFamilyBuilderW14
import ErdosProblems1066.Swanepoel.SwanepoelEndpointAttemptW14
import ErdosProblems1066.Swanepoel.TargetReduction

set_option autoImplicit false

/-!
# W14 face-reduction endpoint bridge

This file is only plumbing: it connects the checked face-reduction facades to
the smallest endpoint-facing family currently available,
`MinimalFailureClosureW13.RemainingInputFamily`.  Every endpoint theorem below
keeps the required uniform minimal-failure or matrix hypothesis explicit.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FaceReductionEndpointW14

open MinimalGraphFacts

universe u

noncomputable section

abbrev Target : Prop :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

abbrev MinimalFailureExclusion : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    Not (IsMinimalClearedFailure C)

abbrev RemainingInputFamily :=
  MinimalFailureClosureW13.RemainingInputFamily

/-! ## Minimal-failure facade to the endpoint family -/

def remainingInputFamily_of_minimalFailureExclusion
    (H : MinimalFailureExclusion) :
    RemainingInputFamily.{u} :=
  RemainingInputFamilyBuilderW14.remainingInputFamily_of_no_minimalClearedFailure
    H

theorem no_minimalClearedFailure_of_remainingInputFamily
    (H : RemainingInputFamily.{u}) :
    MinimalFailureExclusion :=
  H.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne_of_minimalFailureExclusion
    (H : MinimalFailureExclusion) :
    Target :=
  SwanepoelEndpointAttemptW14.targetLowerBoundEightThirtyOne_of_remainingInputFamily.{0}
    (remainingInputFamily_of_minimalFailureExclusion.{0} H)

theorem lower_bound_eight_thirty_one_of_minimalFailureExclusion
    (H : MinimalFailureExclusion)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_minimalFailureExclusion H n C

/-! ## Target-integrated subpolygon matrices -/

def remainingInputFamily_of_directMatrix
    (M : SubpolygonTargetIntegratedW11.DirectMatrix.{u}) :
    RemainingInputFamily.{u} :=
  remainingInputFamily_of_minimalFailureExclusion
    (SubpolygonTargetIntegratedW11.DirectMatrix.no_minimalClearedFailure M)

def remainingInputFamily_of_k23Matrix
    (M : SubpolygonTargetIntegratedW11.K23Matrix.{u}) :
    RemainingInputFamily.{u} :=
  remainingInputFamily_of_minimalFailureExclusion
    (SubpolygonTargetIntegratedW11.K23Matrix.no_minimalClearedFailure M)

def remainingInputFamily_of_commonNeighborMatrix
    (M : SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u}) :
    RemainingInputFamily.{u} :=
  remainingInputFamily_of_minimalFailureExclusion
    (SubpolygonTargetIntegratedW11.CommonNeighborMatrix.no_minimalClearedFailure M)

theorem targetLowerBoundEightThirtyOne_of_directMatrix
    (M : SubpolygonTargetIntegratedW11.DirectMatrix.{u}) :
    Target :=
  SwanepoelEndpointAttemptW14.targetLowerBoundEightThirtyOne_of_remainingInputFamily
    (remainingInputFamily_of_directMatrix M)

theorem targetLowerBoundEightThirtyOne_of_k23Matrix
    (M : SubpolygonTargetIntegratedW11.K23Matrix.{u}) :
    Target :=
  SwanepoelEndpointAttemptW14.targetLowerBoundEightThirtyOne_of_remainingInputFamily
    (remainingInputFamily_of_k23Matrix M)

theorem targetLowerBoundEightThirtyOne_of_commonNeighborMatrix
    (M : SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u}) :
    Target :=
  SwanepoelEndpointAttemptW14.targetLowerBoundEightThirtyOne_of_remainingInputFamily
    (remainingInputFamily_of_commonNeighborMatrix M)

theorem lower_bound_eight_thirty_one_of_directMatrix
    (M : SubpolygonTargetIntegratedW11.DirectMatrix.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_directMatrix M n C

theorem lower_bound_eight_thirty_one_of_k23Matrix
    (M : SubpolygonTargetIntegratedW11.K23Matrix.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_k23Matrix M n C

theorem lower_bound_eight_thirty_one_of_commonNeighborMatrix
    (M : SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_commonNeighborMatrix M n C

/-! ## Face-reduction matrices retaining checked low-degree matches -/

def remainingInputFamily_of_directMatrixWithCheckedLowDegree
    (M : SubpolygonFaceReductionW14.DirectMatrixWithCheckedLowDegree.{u}) :
    RemainingInputFamily.{u} :=
  remainingInputFamily_of_minimalFailureExclusion
    (SubpolygonFaceReductionW14.DirectMatrixWithCheckedLowDegree.no_minimalClearedFailure
      M)

def remainingInputFamily_of_k23MatrixWithCheckedLowDegree
    (M : SubpolygonFaceReductionW14.K23MatrixWithCheckedLowDegree.{u}) :
    RemainingInputFamily.{u} :=
  remainingInputFamily_of_minimalFailureExclusion
    (SubpolygonFaceReductionW14.K23MatrixWithCheckedLowDegree.no_minimalClearedFailure
      M)

def remainingInputFamily_of_commonNeighborMatrixWithCheckedLowDegree
    (M :
      SubpolygonFaceReductionW14.CommonNeighborMatrixWithCheckedLowDegree.{u}) :
    RemainingInputFamily.{u} :=
  remainingInputFamily_of_minimalFailureExclusion
    (SubpolygonFaceReductionW14.CommonNeighborMatrixWithCheckedLowDegree.no_minimalClearedFailure
      M)

theorem targetLowerBoundEightThirtyOne_of_directMatrixWithCheckedLowDegree
    (M : SubpolygonFaceReductionW14.DirectMatrixWithCheckedLowDegree.{u}) :
    Target :=
  SwanepoelEndpointAttemptW14.targetLowerBoundEightThirtyOne_of_remainingInputFamily
    (remainingInputFamily_of_directMatrixWithCheckedLowDegree M)

theorem targetLowerBoundEightThirtyOne_of_k23MatrixWithCheckedLowDegree
    (M : SubpolygonFaceReductionW14.K23MatrixWithCheckedLowDegree.{u}) :
    Target :=
  SwanepoelEndpointAttemptW14.targetLowerBoundEightThirtyOne_of_remainingInputFamily
    (remainingInputFamily_of_k23MatrixWithCheckedLowDegree M)

theorem targetLowerBoundEightThirtyOne_of_commonNeighborMatrixWithCheckedLowDegree
    (M :
      SubpolygonFaceReductionW14.CommonNeighborMatrixWithCheckedLowDegree.{u}) :
    Target :=
  SwanepoelEndpointAttemptW14.targetLowerBoundEightThirtyOne_of_remainingInputFamily
    (remainingInputFamily_of_commonNeighborMatrixWithCheckedLowDegree M)

theorem lower_bound_eight_thirty_one_of_directMatrixWithCheckedLowDegree
    (M : SubpolygonFaceReductionW14.DirectMatrixWithCheckedLowDegree.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_directMatrixWithCheckedLowDegree M n C

theorem lower_bound_eight_thirty_one_of_k23MatrixWithCheckedLowDegree
    (M : SubpolygonFaceReductionW14.K23MatrixWithCheckedLowDegree.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_k23MatrixWithCheckedLowDegree M n C

theorem lower_bound_eight_thirty_one_of_commonNeighborMatrixWithCheckedLowDegree
    (M :
      SubpolygonFaceReductionW14.CommonNeighborMatrixWithCheckedLowDegree.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  targetLowerBoundEightThirtyOne_of_commonNeighborMatrixWithCheckedLowDegree
    M n C

end

end FaceReductionEndpointW14

universe u

/-- Source-specific conditional alias for the W14 face-reduction direct matrix
with checked low-degree matches. -/
theorem lower_bound_eight_thirty_one_of_w14_directFaceReductionMatrix
    (M :
      SubpolygonFaceReductionW14.DirectMatrixWithCheckedLowDegree.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  FaceReductionEndpointW14.lower_bound_eight_thirty_one_of_directMatrixWithCheckedLowDegree
    M n C

/-- Source-specific conditional alias for the W14 face-reduction K23 matrix
with checked low-degree matches. -/
theorem lower_bound_eight_thirty_one_of_w14_k23FaceReductionMatrix
    (M :
      SubpolygonFaceReductionW14.K23MatrixWithCheckedLowDegree.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  FaceReductionEndpointW14.lower_bound_eight_thirty_one_of_k23MatrixWithCheckedLowDegree
    M n C

/-- Source-specific conditional alias for the W14 face-reduction
common-neighbor matrix with checked low-degree matches. -/
theorem lower_bound_eight_thirty_one_of_w14_commonNeighborFaceReductionMatrix
    (M :
      SubpolygonFaceReductionW14.CommonNeighborMatrixWithCheckedLowDegree.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  FaceReductionEndpointW14.lower_bound_eight_thirty_one_of_commonNeighborMatrixWithCheckedLowDegree
    M n C

end Swanepoel

namespace Verified
universe u

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from the
W14 direct face-reduction matrix with checked low-degree matches. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w14_directFaceReductionMatrix
    (M :
      Swanepoel.SubpolygonFaceReductionW14.DirectMatrixWithCheckedLowDegree.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.lower_bound_eight_thirty_one_of_w14_directFaceReductionMatrix
    M n C

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from the
W14 K23 face-reduction matrix with checked low-degree matches. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w14_k23FaceReductionMatrix
    (M :
      Swanepoel.SubpolygonFaceReductionW14.K23MatrixWithCheckedLowDegree.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.lower_bound_eight_thirty_one_of_w14_k23FaceReductionMatrix
    M n C

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound from the
W14 common-neighbor face-reduction matrix with checked low-degree matches. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w14_commonNeighborFaceReductionMatrix
    (M :
      Swanepoel.SubpolygonFaceReductionW14.CommonNeighborMatrixWithCheckedLowDegree.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.lower_bound_eight_thirty_one_of_w14_commonNeighborFaceReductionMatrix
    M n C

end Verified
end ErdosProblems1066
