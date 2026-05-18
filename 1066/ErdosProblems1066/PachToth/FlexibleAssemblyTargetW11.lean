import ErdosProblems1066.PachToth.FlexibleCandidateAssemblyW11
import ErdosProblems1066.PachToth.ArbitraryNBridgeW10
import ErdosProblems1066.PachToth.ArbitraryNExactRemainderClosure
import ErdosProblems1066.PachToth.FinalConditional

set_option autoImplicit false

/-!
# W11 flexible target assembly

This file is a target-facing facade for the flexible W11 candidate route.
It keeps the exact target, the fixed-`n` exact/remainder route, the eventual
threshold, and the finite small-case complement as separate projections.

All rows remain conditional on explicit field packages.  No public bound
wrapper is introduced here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FlexibleAssemblyTargetW11

noncomputable section

universe u

abbrev CandidateFields :=
  FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields

abbrev CandidateValueMatrixFamily :=
  FlexibleCandidateAssemblyW11.CandidateValueMatrixFamily

abbrev PackedCandidateInequalities :=
  FlexibleCandidateAssemblyW11.PackedCandidateInequalities

abbrev FinalConditionalFamily :=
  FinalConditional.EquationPeriodSearchCrossBlockFamily

/-- A target-facing route whose eventual threshold and finite small-case
complement are explicit fields. -/
structure ThresholdSmallCaseRoute (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  threshold : alpha -> Nat
  largeTarget :
    forall a : alpha, forall n : Nat, threshold a <= n ->
      PachToth.targetUpperConstructionFiveSixteenAt n
  smallCases :
    forall a : alpha,
      PachToth.targetUpperConstructionFiveSixteenSmallUpTo (threshold a)

namespace ThresholdSmallCaseRoute

/-- The eventual target obtained from the recorded threshold and large cases. -/
theorem eventualTarget
    {alpha : Sort u} (R : ThresholdSmallCaseRoute alpha) (a : alpha) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  Exists.intro (R.threshold a) (R.largeTarget a)

/-- The arbitrary target obtained from the recorded large and small sides. -/
theorem arbitraryTarget
    {alpha : Sort u} (R : ThresholdSmallCaseRoute alpha) (a : alpha) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
    (R.threshold a)
    (R.largeTarget a)
    (R.smallCases a)

/-- Build a threshold/small-case route from an exact target using the checked
exact/remainder bridge for every fixed vertex count. -/
def ofExactTarget
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (threshold : alpha -> Nat) :
    ThresholdSmallCaseRoute alpha where
  exactTarget := exactTarget
  fixedTarget := fun a n =>
    ArbitraryNExactRemainderClosure.at_of_exactTarget_checkedRemainder
      (exactTarget a) n
  threshold := threshold
  largeTarget := fun a n _hn =>
    ArbitraryNExactRemainderClosure.at_of_exactTarget_checkedRemainder
      (exactTarget a) n
  smallCases := fun a n _hn =>
    ArbitraryNExactRemainderClosure.at_of_exactTarget_checkedRemainder
      (exactTarget a) n

end ThresholdSmallCaseRoute

/-! ## Candidate field route -/

/-- The exact W11 candidate target inherited from the candidate assembly row. -/
theorem exactTarget_of_candidateFields
    (F : CandidateFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  FlexibleCandidateAssemblyW11.targetUpperConstructionFiveSixteen_of_candidateFields
    F

/-- Candidate fields as the W10 exact-target package. -/
def toW10ExactTargetPackage
    (F : CandidateFields) :
    ArbitraryNBridgeW10.ExactTargetPackage where
  exactTarget := exactTarget_of_candidateFields F

/-- The W10 checked-remainder row specialized to W11 candidate fields. -/
def candidateFieldsW10CheckedRemainderRow :
    ArbitraryNBridgeW10.CheckedRemainderRouteRow CandidateFields :=
  ArbitraryNBridgeW10.checkedRemainderRouteRow
    exactTarget_of_candidateFields

/-- The target-facing candidate route with caller-chosen vertex threshold. -/
def candidateFieldsRouteWithThreshold
    (N0 : Nat) :
    ThresholdSmallCaseRoute CandidateFields :=
  ThresholdSmallCaseRoute.ofExactTarget
    exactTarget_of_candidateFields
    (fun _F => N0)

/-- The default W11 target-facing vertex threshold.  The checked fixed-`n`
route discharges both sides of this split. -/
def candidateFieldsVertexThreshold : Nat := 16

/-- The default candidate-field route used by the W11 target matrix. -/
def candidateFieldsRoute :
    ThresholdSmallCaseRoute CandidateFields :=
  candidateFieldsRouteWithThreshold candidateFieldsVertexThreshold

@[simp]
theorem candidateFieldsRoute_threshold
    (F : CandidateFields) :
    candidateFieldsRoute.threshold F = candidateFieldsVertexThreshold :=
  rfl

/-- Fixed-`n` target from candidate fields through the checked exact/remainder
bridge. -/
theorem targetUpperConstructionFiveSixteenAt_of_candidateFields
    (F : CandidateFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  candidateFieldsRoute.fixedTarget F n

/-- Large side of the explicit default threshold split for candidate fields. -/
theorem largeTarget_of_candidateFields
    (F : CandidateFields) (n : Nat)
    (hn : candidateFieldsVertexThreshold <= n) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  candidateFieldsRoute.largeTarget F n (by simpa using hn)

/-- Small-case complement below the explicit default threshold for candidate
fields. -/
theorem smallCases_of_candidateFields
    (F : CandidateFields) :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo
      candidateFieldsVertexThreshold := by
  simpa using candidateFieldsRoute.smallCases F

/-- Eventual target from candidate fields with the default W11 threshold. -/
theorem targetUpperConstructionFiveSixteenEventually_of_candidateFields
    (F : CandidateFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  candidateFieldsRoute.eventualTarget F

/-- Arbitrary target from candidate fields using the explicit threshold and
small-case split. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateFields
    (F : CandidateFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  candidateFieldsRoute.arbitraryTarget F

/-- The same arbitrary target, routed through the W10 checked-remainder row. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateFields_viaW10
    (F : CandidateFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  candidateFieldsW10CheckedRemainderRow.arbitraryTarget F

/-- The same arbitrary target, routed through the W11 candidate assembly row. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateFields_viaAssembly
    (F : CandidateFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  FlexibleCandidateAssemblyW11.targetUpperConstructionFiveSixteenArbitrary_of_candidateFields
    F

/-! ## Packed and value-matrix projections -/

/-- Candidate fields forget to the packed W10 inequality package. -/
def toPackedCandidateInequalities
    (F : CandidateFields) :
    PackedCandidateInequalities :=
  F.packedInequalities

/-- Candidate fields forget to the candidate value-matrix package. -/
def toCandidateValueMatrixFamily
    (F : CandidateFields) :
    CandidateValueMatrixFamily :=
  F.toCandidateValueMatrixFamily

/-- Exact target after forgetting candidate fields to value matrices. -/
theorem exactTarget_of_candidateValueMatrices
    (F : CandidateFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (ArbitraryNBridgeW10.matrix.candidateValueMatrices).exactTarget
    F.toCandidateValueMatrixFamily

/-- Arbitrary target after forgetting candidate fields to value matrices and
using the W10 checked-remainder bridge. -/
theorem arbitraryTarget_of_candidateValueMatrices
    (F : CandidateFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (ArbitraryNBridgeW10.matrix.candidateValueMatrices).arbitraryTarget
    F.toCandidateValueMatrixFamily

/-! ## Final-conditional row -/

/-- Exact target from the final conditional period/equation/cross-block
family. -/
theorem exactTarget_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  FinalConditional.exactTarget_of_periodSearch_equationTransitions_crossBlock
    F

/-- Target-facing final-conditional route with caller-chosen vertex threshold. -/
def finalConditionalRouteWithThreshold
    (N0 : Nat) :
    ThresholdSmallCaseRoute FinalConditionalFamily :=
  ThresholdSmallCaseRoute.ofExactTarget
    exactTarget_of_finalConditionalFamily
    (fun _F => N0)

/-- The final-conditional row at the same default threshold as candidate
fields. -/
def finalConditionalRoute :
    ThresholdSmallCaseRoute FinalConditionalFamily :=
  finalConditionalRouteWithThreshold candidateFieldsVertexThreshold

/-- Eventual target from the final conditional family with explicit threshold
bookkeeping. -/
theorem targetUpperConstructionFiveSixteenEventually_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  finalConditionalRoute.eventualTarget F

/-- Arbitrary target from the final conditional family via the explicit
threshold/small-case split. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  finalConditionalRoute.arbitraryTarget F

/-- The direct final-conditional arbitrary target remains available as a
comparison route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_finalConditionalFamily_direct
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  FinalConditional.arbitraryTarget_of_periodSearch_equationTransitions_crossBlock
    F

/-! ## W11 target matrix -/

/-- The W11 target-facing assembly matrix. -/
structure Matrix where
  candidateFields : ThresholdSmallCaseRoute CandidateFields
  finalConditionalFamily : ThresholdSmallCaseRoute FinalConditionalFamily
  w10CandidateValueMatrices :
    ArbitraryNBridgeW10.CheckedRemainderRouteRow CandidateValueMatrixFamily

/-- The checked W11 target-facing assembly. -/
def matrix : Matrix where
  candidateFields := candidateFieldsRoute
  finalConditionalFamily := finalConditionalRoute
  w10CandidateValueMatrices := ArbitraryNBridgeW10.matrix.candidateValueMatrices

end

end FlexibleAssemblyTargetW11
end PachToth
end ErdosProblems1066
